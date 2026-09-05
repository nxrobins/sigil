//! RANGE-FOR (RF-M0) — the `for v in a..b` exclusive i64 range loop: parse
//! surface + typing + the fail-closed reject matrix. M0 ships the LOOP only
//! (zero elision): every `arr[v]` inside a range body keeps its runtime bounds
//! trap (the memory-safety floor); the compile-time bounds fact + elision are
//! RF-M2/M3. Runtime semantics (sum/break/continue/eval-once/trap) are pinned
//! in crates/sigil-runtime/tests/range_for.rs.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    if let Err(err) = compile_named_module(format!("range_for_{label}.sigil"), source) {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

fn assert_fires(source: &str, label: &str, code: &str) {
    let err = compile_named_module(format!("range_for_{label}.sigil"), source)
        .err()
        .unwrap_or_else(|| panic!("expected {code} for {label}, but compile succeeded"));
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&code),
        "expected {code} in diagnostics for {label}, got: {codes:?}"
    );
}

// ── Accepts ──────────────────────────────────────────────────────────────────

#[test]
fn basic_range_loop_compiles() {
    assert_compiles_clean(
        r#"
module main;
fn sum_to(n: i64) -> i64 {
    let mut acc = 0;
    for i in 0..n {
        acc = acc + i;
    }
    return acc;
}
"#,
        "basic",
    );
}

#[test]
fn literal_bounds_compile() {
    // Both bounds literal — the PIL narrowing must leave no IntLit for AIR.
    assert_compiles_clean(
        r#"
module main;
fn f() -> i64 {
    let mut acc = 0;
    for i in 0..10 {
        acc = acc + 1;
    }
    return acc;
}
"#,
        "literal_bounds",
    );
}

#[test]
fn nested_and_break_continue_compile() {
    assert_compiles_clean(
        r#"
module main;
fn f() -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        for j in 0..4 {
            if j == 2 {
                continue;
            }
            if i == 2 {
                break;
            }
            acc = acc + 1;
        }
    }
    return acc;
}
"#,
        "nested_break_continue",
    );
}

#[test]
fn array_index_in_body_compiles_with_trap_floor() {
    // M0: `a[i]` inside the body keeps its RUNTIME bounds check (no elision
    // yet) — but it must COMPILE (the loop var is an ordinary i64 local).
    assert_compiles_clean(
        r#"
module main;
fn f(a: [i64; 3]) -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        acc = acc + a[i];
    }
    return acc;
}
"#,
        "index_trap_floor",
    );
}

#[test]
fn expr_bounds_compile() {
    // Arbitrary i64 exprs as bounds — the loop is total; only the FACT
    // (RF-M2) requires the resolvable subset.
    assert_compiles_clean(
        r#"
module main;
fn f(lo: i64, hi: i64) -> i64 {
    let mut acc = 0;
    for i in lo + 1..hi * 2 {
        acc = acc + 1;
    }
    return acc;
}
"#,
        "expr_bounds",
    );
}

// ── Rejects (fail-closed) ────────────────────────────────────────────────────

#[test]
fn inclusive_range_rejected_p029() {
    // `..=` in a for header — one canonical loop form (no off-by-one variant
    // for the bounds machinery or the SH-AIR shadow to mis-derive).
    assert_fires(
        r#"
module main;
fn f() -> i64 {
    for i in 0..=3 {
    }
    return 0;
}
"#,
        "inclusive",
        "P029",
    );
}

#[test]
fn bool_end_bound_rejected_t280() {
    assert_fires(
        r#"
module main;
fn f() -> i64 {
    for i in 0..true {
    }
    return 0;
}
"#,
        "bool_end",
        "T280",
    );
}

#[test]
fn bool_start_bound_rejected_t280() {
    assert_fires(
        r#"
module main;
fn f() -> i64 {
    for i in false..3 {
    }
    return 0;
}
"#,
        "bool_start",
        "T280",
    );
}

#[test]
fn loop_var_reassignment_rejected_t042() {
    // THE load-bearing immutability: the induction variable is never in
    // `mutables`, so assignment is a hard error — this is what later makes
    // the range a trustworthy compile-time bounds fact (RF-M2) with no flow
    // tracking.
    assert_fires(
        r#"
module main;
fn f() -> i64 {
    for i in 0..3 {
        i = 99;
    }
    return 0;
}
"#,
        "reassign",
        "T042",
    );
}

#[test]
fn secret_bound_rejected_t022() {
    // The bounds ARE the iteration count — a @SecretCT bound is
    // secret-dependent iteration (CT003), same as ForIn's iterable.
    assert_fires(
        r#"
module main;
fn f(n: i64 @SecretCT) -> i64 ! {} {
    let mut acc = 0;
    for i in 0..n {
        acc = acc + 1;
    }
    return acc;
}
"#,
        "secret_bound",
        "T022",
    );
}

// ── Security-walker proofs (the hand-audited arms actually fire) ─────────────

#[test]
fn range_for_inside_region_rejected_t068() {
    // capability_tc's control-flow tuple got a ForRange arm — a range loop
    // inside a `region` body must reject like every other control-flow form.
    assert_fires(
        r#"
module main;
fn f() -> i64 ! { Alloc } {
    region scratch(64) {
        for i in 0..3 {
        }
    };
    return 0;
}
"#,
        "in_region",
        "T068",
    );
}

#[test]
fn owned_cap_inside_range_body_rejected_r001() {
    // ring_check::check_outer_body is a FAIL-OPEN (`_ => {}`) walker — this
    // test proves its hand-added ForRange arm: an owned-cap `let` inside a
    // range-for body in an outer-ring fn must still hit R001, not silently
    // slip the scan.
    assert_fires(
        r#"
#[ring(outer)]
module main;
cap type Tool { use_tool }
fn f() -> i64 ! {} {
    for i in 0..3 {
        let c: Tool = make();
    }
    return 0;
}
fn make() -> Tool ! {} {
    return make();
}
"#,
        "cap_in_body",
        "R001",
    );
}

#[test]
fn effect_leak_inside_range_body_rejected_e001() {
    // effect_check's walk_stmts got a ForRange arm — a call to an effectful
    // fn inside a range body must still count against the caller's row.
    assert_fires(
        r#"
#[ring(outer)]
module main;
effect Net;
fn leaf() -> i64 ! { Net } {
    return 1;
}
fn f() -> i64 ! {} {
    let mut acc = 0;
    for i in 0..3 {
        acc = acc + leaf();
    }
    return acc;
}
"#,
        "effect_leak",
        "E001",
    );
}

#[test]
fn shadowing_let_rebinds_cleanly() {
    // A `let i = …` inside the body SHADOWS the loop var (an ordinary new
    // binding) — must compile. RF-M2's fact pre-scan will refuse the bounds
    // fact for this shape, but the LOOP itself is fine.
    assert_compiles_clean(
        r#"
module main;
fn f() -> i64 {
    let mut acc = 0;
    for i in 0..3 {
        let i = 100;
        acc = acc + i;
    }
    return acc;
}
"#,
        "shadow_let",
    );
}

// ── RF-M3: the T278 per-execution reject (source c) ──────────────────────────

#[test]
fn always_oob_guard_rejected_t278() {
    // Inside `if i >= 5` within 0..10, the composed interval is [5,9] —
    // ENTIRELY >= N=5: every execution of this access traps. Same
    // per-execution claim as the literal `a[7]` T278; compile-time reject.
    assert_fires(
        r#"
module main;
fn f(a: [i64; 5]) -> i64 {
    let mut acc = 0;
    for i in 0..10 {
        if i >= 5 {
            acc = acc + a[i];
        }
    }
    return acc;
}
"#,
        "always_oob_guard",
        "T278",
    );
}

#[test]
fn else_branch_negation_rejected_t278() {
    // The ELSE of `i < 5` composes the negated clause (i >= 5) — the same
    // always-OOB interval through the negation path.
    assert_fires(
        r#"
module main;
fn f(a: [i64; 5]) -> i64 {
    let mut acc = 0;
    for i in 0..10 {
        if i < 5 {
            acc = acc + 1;
        } else {
            acc = acc + a[i];
        }
    }
    return acc;
}
"#,
        "else_negation_oob",
        "T278",
    );
}
