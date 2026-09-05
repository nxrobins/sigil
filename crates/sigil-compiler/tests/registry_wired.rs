//! Phase 5a-1.6 / I13 / AP11: fixture-per-code wiring test.
//!
//! For every diagnostic code in `CODES`, there must exist a fixture
//! that triggers emission OR a documented exemption. The framework
//! supports two fixture kinds:
//!
//! 1. **Source fixture**: `tests/fixtures/<CODE>.sigil` — a Sigil source
//!    that, when compiled, emits a diagnostic with `code == CODE`.
//! 2. **Programmatic fixture**: the file contains the sentinel
//!    `SENTINEL_PROGRAMMATIC` and the test driver knows how to
//!    construct the triggering source at test time. This is for codes
//!    whose triggering input is too large or awkward to write by hand
//!    (e.g., S004 needs 257 module declarations).
//!
//! ### Reporting backlog
//!
//! Codes that lack a fixture are NOT a hard test failure today — they're
//! reported as a backlog. The 5a-1.6 PR establishes the framework and
//! provides fixtures for codes added in 5a-1 / 5a-1.5 / 5a-1.6 (the ones
//! at most risk of AP11 — "documented but never emitted"). Pre-existing
//! codes get fixtures in subsequent corpus PRs.
//!
//! Fail-mode is gated on the `strict_registry` feature. Default behavior
//! reports the backlog count and exits 0.

use std::collections::HashSet;
use std::path::PathBuf;

use sigil_compiler::compile_named_module;
use sigil_compiler::diagnostics::registry::CODES;

/// Minimum code coverage 5a-1.6 expects. Every code added in 5a-1
/// (PR #18), 5a-1.5 (PR #19), and 5a-1.6 (this PR) must have a working
/// fixture. Existing pre-5a codes are tracked as backlog.
const REQUIRED_FIXTURE_CODES: &[&str] = &[
    // Phase 5a-1 (cross-module substrate, PR #18)
    "N007", "N008", "N009", "T155", "R004", // Phase 5a-1.5 (hardening, PR #19)
    "S004", "S005", "S006", "N011", "T156",
    // N012 is registry-presence only (case-collision is gated by N011);
    // documented as exempt below.
    //
    // Axis-7 enforcement ratchet (diagnostics-axes loop): pre-5a codes that
    // already ship a committed, emitting fixture are promoted from the
    // non-blocking backlog to hard-required. Enforced by
    // `all_present_fixtures_are_required`, which forbids any fixture from
    // regressing back to the backlog.
    "E003", "R003", "R006", "T043", "T046", "T140", "T183", "T184", "T185", "T186", "T190", "T191",
    "T192", "T193", "T195", "T196", "T197", "T198", "T200", "T201",
    // Actor-state (M2): assigning state in a handler (immutable after `init`).
    "T123",
    // Actor-state (M4): consuming a borrow-only state cap in an ordinary handler
    // (permitted only at construction — `init` / entry `Start`).
    "C010",
    // Actor-state (M4): a closure may not capture an actor state field (no access
    // to the state pointer; also closes the closure cap-laundering channel).
    "T127",
    // Actor-state (MUTABLE-STATE S1): the `mut` marker is state-only — a record
    // field carrying `mut` is rejected (the fixture is a record with a `mut` field).
    "P030",
    // Actor-state (MUTABLE-STATE S2 / F1, the decider): a `mut` state field must be
    // plain reassignable data — a cap/ref/borrow-bearing `mut` field is rejected.
    "C011",
    // Actor-state (MUTABLE-STATE S2 / F3, definite-assignment): every state field must
    // be assigned exactly once, unconditionally, in `init` (T124 double / T125 missing).
    "T124", "T125",
    // T242 (cap-smuggle through a generic aggregate) gained a committed
    // fixture (tuple type-arg variant) once `type_contains_cap` was made to
    // recurse into Tuple/Fn — promote it to hard-required so the gate's
    // emission can never silently regress.
    "T242",
    // Effect handlers (EH0): the intermediate-rung gate (E004) ships a committed
    // fixture (`perform` rejected until the type-check rung lands), so its
    // emission is hard-required from the start.
    "E004",
    // Effect handlers (EH1): perform shape-checking — unknown op / unknown
    // effect / wrong arg count.
    "E005", "E006", "E007",
    // Effect handlers (EH2): clause-handle coverage / bare-handle-on-op-effect.
    "E008", "E009", // Effect handlers (EH3): orphan-perform of an undeclared effect.
    "E010",
    // Row polymorphism (Phase 4): invalid effect-row variable — the fixture is
    // a binder shadowing a declared effect (kind-by-use's ambiguous shape).
    "E011",
    // Phase 4 post-merge sweep: ref/slice of a function type — previously a
    // SILENT structure drop (the parser discarded the element's fn_type, so
    // its effect row vanished undiagnosed), now a hard error.
    "T281",
    // Range-for (RF-M0): `..=` rejected in a `for` header / non-i64 range bound.
    "P029", "T280",
    // Match ranges: a `lo..=hi` bound that is not an integer literal. The
    // parser shares its range arm with literal patterns, so `"a"..="z"` and
    // `true..=false` reached AIR, were coerced to `0`, and killed the build
    // at the wasm backstop instead of naming the source-level mistake.
    "T282",
    // CT018: `str` `==`/`!=` with a `@SecretCT` operand. Content comparison is
    // an early-exit byte loop, so its trip count AND its fuel reveal the
    // common-prefix length. Rejected rather than lowered constant-time —
    // `ct_eq`/`ct_select`/`ct_lt` are integer-only, so there is nothing to
    // build a constant-time `str` compare from.
    "T033",
];

/// Codes documented as exempt from the fixture requirement, with
/// reason. New entries here require code-review justification.
///
/// R8xx codes are exempt by-prefix (see `is_exempt_by_prefix` below);
/// they're runtime feedback re-emitted by sigil-mcp / sigil-cli, not
/// compiler-emitted, so they have no source-fixture form. Their
/// emission is verified by tests in `sigil-runtime/tests/` and
/// `sigil-mcp/tests/`.
const FIXTURE_EXEMPT: &[(&str, &str)] = &[
    (
        "N012",
        "case-collision is gated by N011 firing first; case-only-different module names with both well-formed cannot occur because uppercase fails N011",
    ),
    (
        "I001",
        "internal compiler error — cannot be triggered by valid AST",
    ),
    (
        "T199",
        "build-time-stale deadline check requires `--build-deadline <N>` on the compile call; the default `compile_named_module` path does not provide it. Covered by tests/wall2_step2_build_deadline.rs via `compile_named_module_with_options`.",
    ),
];

/// Codes whose entire prefix is documented exempt. R8xx is the runtime-
/// feedback range; codes there are emitted from sigil-runtime / sigil-mcp
/// / sigil-cli, not the compiler proper.
fn is_exempt_by_prefix(code: &str) -> bool {
    code.starts_with('R')
        && code
            .get(1..2)
            .and_then(|s| s.chars().next())
            .map(|c| c == '8')
            .unwrap_or(false)
}

const FIXTURES_DIR: &str = "tests/fixtures";
const SENTINEL_PROGRAMMATIC: &str = "SENTINEL_PROGRAMMATIC";

fn fixture_path(code: &str) -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push(FIXTURES_DIR);
    p.push(format!("{code}.sigil"));
    p
}

fn programmatic_source_for(code: &str) -> Option<String> {
    match code {
        "S004" => {
            // Cap is 256; 257 modules trigger.
            let mut s = String::new();
            for i in 0..=256 {
                s.push_str(&format!("module m{i};\n"));
            }
            Some(s)
        }
        "S005" => {
            // Cap is 5 MB; one module + comment padding past the cap.
            let target = 5 * 1024 * 1024 + 1;
            let mut s = String::from("module main;\n");
            let line = "// padding line\n";
            while s.len() < target {
                s.push_str(line);
            }
            Some(s)
        }
        "S006" => {
            // Cap is 10,000 fns; produce 10,001.
            let mut s = String::from("module m;\n");
            for i in 0..=10_000 {
                s.push_str(&format!("fn f{i}() -> i64 {{ return {i}; }}\n"));
            }
            Some(s)
        }
        _ => None,
    }
}

#[test]
fn registry_codes_have_fixtures() {
    let mut registered: Vec<&str> = CODES.iter().map(|e| e.code.as_str()).collect();
    registered.sort();

    let exempt: HashSet<&str> = FIXTURE_EXEMPT.iter().map(|(c, _)| *c).collect();
    let required: HashSet<&str> = REQUIRED_FIXTURE_CODES.iter().copied().collect();

    let mut missing_required: Vec<&str> = Vec::new();
    let mut backlog: Vec<&str> = Vec::new();
    let mut fixture_present_but_doesnt_emit: Vec<String> = Vec::new();

    for code in &registered {
        if exempt.contains(code) || is_exempt_by_prefix(code) {
            continue;
        }
        let path = fixture_path(code);
        if !path.exists() {
            if required.contains(code) {
                missing_required.push(code);
            } else {
                backlog.push(code);
            }
            continue;
        }
        // Fixture exists: verify it triggers the code.
        let source = if let Some(generated) = programmatic_source_for(code) {
            generated
        } else {
            std::fs::read_to_string(&path).expect("fixture readable")
        };
        // Skip the sentinel-only stub if we don't have a programmatic
        // source for it — the fixture is just a marker.
        if source.contains(SENTINEL_PROGRAMMATIC) && programmatic_source_for(code).is_none() {
            fixture_present_but_doesnt_emit.push(format!(
                "{code}: fixture is sentinel but no programmatic source registered"
            ));
            continue;
        }
        match compile_named_module(format!("{code}_fixture"), source) {
            Ok(_) => {
                fixture_present_but_doesnt_emit.push(format!(
                    "{code}: fixture compiled cleanly — code never emitted"
                ));
            }
            Err(err) => {
                let emitted: Vec<&str> = err
                    .diagnostics()
                    .iter()
                    .map(|d| d.code().as_str())
                    .collect();
                if !emitted.iter().any(|c| c == code) {
                    fixture_present_but_doesnt_emit.push(format!(
                        "{code}: fixture failed to compile but did NOT emit {code}; got: {:?}",
                        emitted
                    ));
                }
            }
        }
    }

    assert!(
        missing_required.is_empty(),
        "I13: codes added in 5a-1/5a-1.5/5a-1.6 lack required fixtures: {:?}",
        missing_required
    );
    assert!(
        fixture_present_but_doesnt_emit.is_empty(),
        "I13 / AP11: fixtures exist but don't actually trigger the code:\n{}",
        fixture_present_but_doesnt_emit.join("\n")
    );

    if !backlog.is_empty() {
        eprintln!(
            "I13 backlog: {} pre-5a codes lack fixtures (tracked, not blocking): {:?}",
            backlog.len(),
            backlog
        );
    }
}

/// Axis-7 enforcement ratchet (diagnostics-axes loop): once a code has a
/// committed fixture, its emission is HARD-enforced — the code must be listed
/// in `REQUIRED_FIXTURE_CODES`. This forbids a fixture silently regressing to
/// the non-blocking backlog and forces every newly-added fixture to be wired as
/// required, so enforcement only ever ratchets forward.
#[test]
fn all_present_fixtures_are_required() {
    let required: HashSet<&str> = REQUIRED_FIXTURE_CODES.iter().copied().collect();
    let exempt: HashSet<&str> = FIXTURE_EXEMPT.iter().map(|(c, _)| *c).collect();

    let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    dir.push(FIXTURES_DIR);

    let mut not_required: Vec<String> = Vec::new();
    for entry in std::fs::read_dir(&dir).expect("fixtures dir readable") {
        let path = entry.expect("dir entry").path();
        if path.extension().and_then(|s| s.to_str()) != Some("sigil") {
            continue;
        }
        let code = path
            .file_stem()
            .and_then(|s| s.to_str())
            .expect("fixture stem is valid UTF-8")
            .to_owned();
        if exempt.contains(code.as_str()) || is_exempt_by_prefix(&code) {
            continue;
        }
        if !required.contains(code.as_str()) {
            not_required.push(code);
        }
    }
    not_required.sort();

    assert!(
        not_required.is_empty(),
        "axis 7: these codes have a fixture but are not in REQUIRED_FIXTURE_CODES \
         (a fixture means the emission is enforced — add them to the required \
         list):\n  {}",
        not_required.join(", ")
    );
}
