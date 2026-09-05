//! Self-hosting Cap<Z3>: static source contract for the `z3_check` shim.
//!
//! Realizes the CM1/CM2/CM3/CM4 Fail-Fast modes as a text scan of
//! `src/ephemeral.rs`. Deliberately NOT feature-gated: it reads source text
//! (cfg'd code is still present in the file), so it runs in every build and
//! cannot be silently skipped. Pairs with the behavioral proof tests in
//! `z3_capability_shim.rs` (gated on `--features solver`).

use std::path::PathBuf;

fn ephemeral_src() -> String {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("src");
    p.push("ephemeral.rs");
    std::fs::read_to_string(&p).expect("read src/ephemeral.rs")
}

/// Substring between `start` (inclusive) and the next `end` after it
/// (exclusive). Panics if either marker is missing.
fn region<'a>(src: &'a str, start: &str, end: &str) -> &'a str {
    let s = src
        .find(start)
        .unwrap_or_else(|| panic!("start marker not found: {start}"));
    let e = src[s..]
        .find(end)
        .unwrap_or_else(|| panic!("end marker not found after start: {end}"))
        + s;
    &src[s..e]
}

/// The z3_check shim closure body: from its `func_wrap` name to the solve
/// call that terminates it.
fn shim_region(src: &str) -> &str {
    region(src, "\"z3_check\"", "z3_solve_smtlib2(&query)")
}

/// The deterministic solver helper body.
fn solve_region(src: &str) -> &str {
    region(src, "fn z3_solve_smtlib2_with_rlimit", "\n#[cfg(all(test")
}

/// Drop `//`-comment text (full-line and trailing) so the contract scans only
/// executable code, not prose. No `//` appears inside string literals in the
/// scanned regions, so a naive split is safe here.
fn strip_comments(region: &str) -> String {
    region
        .lines()
        .map(|line| match line.find("//") {
            Some(i) => &line[..i],
            None => line,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn cm2_grant_check_precedes_solver_work() {
    let src = ephemeral_src();
    let shim = shim_region(&src);
    let allowed = shim
        .find("z3_allowed()")
        .expect("CM2: shim must check z3_allowed()");
    assert!(
        shim.contains("pack_error(403)"),
        "CM2: shim must fail closed with 403"
    );
    // No work before authority: the grant check must precede the first guest
    // memory access (and therefore all parse/solver work that follows it).
    let first_work = shim
        .find("get_guest_memory_and_bump")
        .expect("CM2: shim must fetch guest memory");
    assert!(
        allowed < first_work,
        "CM2: grant check must precede guest-memory/parse/solver work"
    );
}

#[test]
fn cm1_unknown_maps_to_negative_never_verdict() {
    let src = ephemeral_src();
    let solve = solve_region(&src);
    assert!(
        solve.contains("SatResult::Unknown"),
        "CM1: must handle the Unknown outcome"
    );
    assert!(
        solve.contains("pack_error(408)"),
        "CM1: Unknown must map to the distinct negative code -408"
    );
    assert!(
        !solve.contains("Unknown => 0"),
        "CM1: Unknown must NEVER be reported as unsat(0)"
    );
    assert!(
        !solve.contains("Unknown => 1"),
        "CM1: Unknown must NEVER be reported as sat(1)"
    );
    // The parse-error gate: zero parsed assertions ⇒ malformed, never a verdict.
    assert!(
        solve.contains("get_assertions().is_empty()"),
        "CM1/MI3: must reject zero-assertion (malformed) queries before check()"
    );
}

#[test]
fn cm3_no_panicking_unwrap_on_guest_input() {
    let src = ephemeral_src();
    // Strip comments first: prose may legitimately *mention* `.unwrap()` (the
    // shim documents why z3's from_string would panic on a NUL).
    let shim = strip_comments(shim_region(&src));
    assert!(
        !shim.contains(".unwrap(") && !shim.contains(".expect("),
        "CM3: the shim must not .unwrap()/.expect() on guest-derived data"
    );
    let solve = strip_comments(solve_region(&src));
    assert!(
        !solve.contains(".unwrap(") && !solve.contains(".expect("),
        "CM3: the solver helper must not .unwrap()/.expect()"
    );
    // The interior-NUL guard (z3's from_string would panic on it) is real code.
    assert!(
        shim_region(&src).contains("contains(&0)"),
        "CM3: the shim must reject interior-NUL queries before from_string"
    );
}

#[test]
fn cm4_rlimit_bounded_never_walltime() {
    let src = ephemeral_src();
    let solve = solve_region(&src);
    assert!(
        solve.contains("set_u32(\"rlimit\""),
        "CM4: solve must be bounded by an rlimit (solver fuel)"
    );
    assert!(
        !solve.contains("timeout"),
        "CM4: solve must NOT use a wall-clock timeout (nondeterministic)"
    );
}
