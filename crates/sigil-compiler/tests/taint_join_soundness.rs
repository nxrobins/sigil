//! Taint soundness at control-flow merge points (docs/specs/taint-join-soundness.md).
//!
//! FOUND BY AN INDEPENDENT REVIEW, not by this project's own audit. `taint_check.rs`'s branching
//! arms save and restore only `pc_taint` and run every branch against the same `&mut env`.
//! `TaintEnv` is one flat map per function; assignment to a bare local is a strong-update relabel
//! (`Assign` → `env.bind(name, effective)`, taint_check.rs:202) with NO downgrade check — the label
//! FLOATS. So the last branch analysed wins:
//!
//! ```ignore
//! let mut x: i64 = 0;               // @Public
//! if c { x = s; } else { x = 0; }  // then relabels x @Secret, else relabels it back @Public
//! return x;                        // sees @Public — the secret vanished. ACCEPTED.
//! ```
//!
//! THE MODEL, grounded (taint_check.rs):
//!   * `let x: i64 = <secret>` PINS to the declared label and runs a `can_flow_to` downgrade check
//!     (:168) → T001 AT THE DECLARATION. So `let mut x = s` is the WRONG way to get a secret into a
//!     variable for these tests — it fails before any branch/loop is reached (a false green that
//!     bit the first draft of this file).
//!   * `x = <secret>` (Assign to a bare Local, :202) is a pure relabel, no check — this is how a
//!     variable legitimately comes to hold a secret via flow.
//!   * the sink that SHOULD catch the leak is the return check (:388): "returning @Secret value
//!     from function declared @Public". Every rejection assertion below pins THAT message, so a
//!     program rejected for some other reason (e.g. a declaration downgrade) does not count as a
//!     pass — the test is tied to the join hazard, not to rejection-in-general.
//!
//! THE LOOP HAZARD RUNS THE OTHER WAY. `x = secret; while c { x = 0; }` — the body may run ZERO
//! times, so `x` can still be @Secret at the return; the buggy analysis sees the body's `x = 0` and
//! reports @Public. A loop must join the body result with the zero-iteration (pre-loop) state.

use sigil_compiler::CompileError;
use sigil_compiler::compile_named_module;

/// The distinctive fragment of the return-sink T001 message (taint_check.rs:392). Pinning this,
/// rather than the bare code "T001", ties every assertion below to the sink we mean — a leak caught
/// at a `let` downgrade or anywhere else carries a different message and does NOT satisfy it.
const RETURN_SINK_MSG: &str = "returning @Secret value from function declared @Public";

fn err_debug(e: &CompileError) -> String {
    format!("{e:?}")
}

/// A program that leaks a secret on ONE control-flow path MUST be rejected at the return sink.
/// Before the fix this panics "SOUNDNESS HOLE" because the program compiles (the leak is lost at
/// the merge). After the fix it is rejected with the return-sink message.
fn assert_leak_rejected(name: &str, source: &str, why: &str) {
    match compile_named_module(name, source) {
        Ok(_) => panic!("SOUNDNESS HOLE: {why}\n--- source ---\n{source}"),
        Err(e) => {
            let d = err_debug(&e);
            assert!(
                d.contains(RETURN_SINK_MSG),
                "rejected, but NOT at the return sink — the test is not measuring the join \
                 hazard.\nwanted a message containing: {RETURN_SINK_MSG:?}\ngot: {d}\n\
                 --- source ---\n{source}"
            );
        }
    }
}

fn assert_compiles(name: &str, source: &str, why: &str) {
    if let Err(e) = compile_named_module(name, source) {
        panic!(
            "{why}\ngot rejection: {}\n--- source ---\n{source}",
            err_debug(&e)
        );
    }
}

// ── If: the merge must be a LUB, not "last branch wins" ──────────────────────────────────────

/// TRUE RED. `x` is relabelled @Secret in the then-branch (a float, not a downgrade); the else
/// branch relabels it back @Public, and because both run against one env the return sees @Public.
#[test]
fn if_else_secret_on_then_path_is_rejected() {
    assert_leak_rejected(
        "join_then.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, c: bool) -> i64 {
    let mut x: i64 = 0;
    if c {
        x = s;
    } else {
        x = 0;
    }
    return x;
}
"#,
        "a @Secret assigned on the THEN path reaches a @Public return; the else branch overwrote \
         the shared binding",
    );
}

/// STAYS-REJECTED guard. The else branch runs last, so this leak is caught even by the buggy
/// analysis. It guards against a "fix" that merely swaps WHICH path is lost.
#[test]
fn if_else_secret_on_else_path_stays_rejected() {
    assert_leak_rejected(
        "join_else.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, c: bool) -> i64 {
    let mut x: i64 = 0;
    if c {
        x = 0;
    } else {
        x = s;
    }
    return x;
}
"#,
        "a @Secret assigned on the ELSE path reaches a @Public return",
    );
}

// ── Match: the same defect across arms ───────────────────────────────────────────────────────

/// TRUE RED. Arms share one env; the last arm (`Choice::B`) relabels `x` @Public, so a @Secret
/// bound in the first arm is lost at the merge. Uses the QUALIFIED nullary form — a bare `A` parses
/// as a catch-all binder (T080), a fixture bug rather than the hazard under test.
#[test]
fn match_arm_secret_is_rejected() {
    assert_leak_rejected(
        "join_match.sigil",
        r#"module sigil;
enum Choice { A, B }
fn leak(s: i64 @Secret, ch: Choice) -> i64 {
    let mut x: i64 = 0;
    match ch {
        Choice::A => { x = s; },
        Choice::B => { x = 0; },
    }
    return x;
}
"#,
        "a @Secret assigned in the first match arm is overwritten by the last arm at the merge",
    );
}

// ── Loops: the ZERO-ITERATION path is the unsound one ────────────────────────────────────────
//
// The secret enters `x` by FLOW (`x = s`, a relabel), never by declaration — a `let mut x = s`
// would be rejected at the declaration and never exercise the loop join at all.

/// TRUE RED. `x` is @Secret before the loop; the body relabels it @Public. At zero iterations `x`
/// is still @Secret at runtime, so the merge must join body-result with the pre-loop state.
#[test]
fn while_zero_iteration_path_preserves_secret() {
    assert_leak_rejected(
        "join_while.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, c: bool) -> i64 {
    let mut x: i64 = 0;
    x = s;
    while c {
        x = 0;
    }
    return x;
}
"#,
        "the `while` body may run ZERO times, so `x` can still be @Secret at the return",
    );
}

/// TRUE RED. The `for` range may be empty — same zero-iteration hazard.
#[test]
fn for_range_zero_iteration_path_preserves_secret() {
    assert_leak_rejected(
        "join_for.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, n: i64) -> i64 {
    let mut x: i64 = 0;
    x = s;
    for i in 0..n {
        x = 0;
    }
    return x;
}
"#,
        "a `for` range may be empty, so `x` can still be @Secret at the return",
    );
}

/// TRUE RED. `for x in arr` — an empty array runs the body zero times, the SAME zero-iteration
/// hazard as the range form. A distinct construct (SC-T4 wants a test per construct), so a future
/// walker edit that drops the `ForIn` arm fails by name.
#[test]
fn for_in_zero_iteration_path_preserves_secret() {
    assert_leak_rejected(
        "join_forin.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, arr: [i64; 4]) -> i64 {
    let mut x: i64 = 0;
    x = s;
    for v in arr {
        x = 0;
    }
    return x;
}
"#,
        "a `for..in` over an array may be empty, so `x` can still be @Secret at the return",
    );
}

/// TRUE RED — SECOND-ORDER flow. A one-pass loop join would miss this: after iteration 1 `x` holds
/// `y`'s (public) taint and `y` becomes @Secret; only a SECOND pass propagates the secret into `x`.
/// The fixpoint (not a single body pass) is what makes this sound.
#[test]
fn while_second_order_flow_is_rejected() {
    assert_leak_rejected(
        "join_while_2nd.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, c: bool) -> i64 {
    let mut x: i64 = 0;
    let mut y: i64 = 0;
    while c {
        x = y;
        y = s;
    }
    return x;
}
"#,
        "second-order loop flow: x picks up y's secret only on the 2nd iteration; the fixpoint must catch it",
    );
}

// ── Controls: safe programs must still COMPILE ───────────────────────────────────────────────
//
// Without these, "reject everything" passes every test above. A fix that also rejects safe
// programs is a different bug.

#[test]
fn public_only_branches_still_compile() {
    assert_compiles(
        "join_public.sigil",
        r#"module sigil;
fn safe(a: i64, b: i64, c: bool) -> i64 {
    let mut x: i64 = 0;
    if c {
        x = a;
    } else {
        x = b;
    }
    return x;
}
"#,
        "a program with no @Secret anywhere must still compile after the join fix",
    );
}

/// A @Secret flowing to a @Secret return is sound and must still compile — guards against a fix
/// that over-taints and rejects safe programs.
#[test]
fn secret_on_both_paths_to_secret_return_compiles() {
    assert_compiles(
        "join_secret_ok.sigil",
        r#"module sigil;
fn ok(s: i64 @Secret, c: bool) -> i64 @Secret {
    let mut x: i64 @Secret = s;
    if c {
        x = s;
    } else {
        x = s;
    }
    return x;
}
"#,
        "a @Secret flowing to a @Secret return is sound and must compile",
    );
}

/// EXHAUSTIVE match where EVERY arm lowers `x` to @Public → `x` is @Public at the merge and the
/// program must COMPILE. This is the case a `pre`-fall-through branch would wrongly over-taint;
/// merging arms-only (backed by exhaustiveness, T087) is what keeps it accepted.
#[test]
fn match_all_arms_public_compiles() {
    assert_compiles(
        "join_match_ok.sigil",
        r#"module sigil;
enum Choice { A, B }
fn ok(s: i64 @Secret, ch: Choice) -> i64 {
    let mut x: i64 = 0;
    x = s;
    match ch {
        Choice::A => { x = 0; },
        Choice::B => { x = 0; },
    }
    return x;
}
"#,
        "every match arm lowers x to @Public, so x is @Public at the merge — must compile",
    );
}

/// A `while` whose body only ever holds @Public values must still compile — guards against a loop
/// fixpoint that spuriously over-taints.
#[test]
fn while_public_body_compiles() {
    assert_compiles(
        "join_while_ok.sigil",
        r#"module sigil;
fn ok(a: i64, c: bool) -> i64 {
    let mut x: i64 = 0;
    while c {
        x = a;
    }
    return x;
}
"#,
        "a while loop with no @Secret anywhere must compile after the loop-join fix",
    );
}

// ── Property-based: the If join IS the lub (SC-T1, spec P1) ───────────────────────────────────
//
// The join must be exactly the least-upper-bound of the branch taints — no more, no less. For
// labels a, b drawn from the taint lattice, the two-branch program
//   `if c { x = <a> } else { x = <b> }; return x`
// must have the SAME accept/reject verdict as the straight-line `x = <lub(a,b)>; return x`. This is
// stronger than the example-based tests above: it quantifies over the lattice rather than checking
// one point, and it fails both for UNDER-tainting (the original bug: else wins, so (Secret,Public)
// was wrongly accepted) and for OVER-tainting (a "fix" that rejects (Public,Public)).
mod props {
    use super::*;
    use proptest::prelude::*;

    /// Source expression producing a value at taint level `k` (0=Public, 1=Internal, 2=Secret).
    /// `i` and `s` are params of the harness functions below.
    fn src(k: usize) -> &'static str {
        match k {
            0 => "0",
            1 => "i",
            _ => "s",
        }
    }

    proptest! {
        #[test]
        fn if_join_equals_lub(a in 0usize..3, b in 0usize..3) {
            let two = format!(
                "module sigil;
                 fn f(i: i64 @Internal, s: i64 @Secret, c: bool) -> i64 {{
                     let mut x: i64 = 0;
                     if c {{ x = {}; }} else {{ x = {}; }}
                     return x;
                 }}
",
                src(a), src(b)
            );
            let lub = a.max(b);
            let straight = format!(
                "module sigil;
                 fn f(i: i64 @Internal, s: i64 @Secret) -> i64 {{
                     let mut x: i64 = 0;
                     x = {};
                     return x;
                 }}
",
                src(lub)
            );
            let two_ok = compile_named_module("p_two.sigil", &two).is_ok();
            let straight_ok = compile_named_module("p_straight.sigil", &straight).is_ok();
            prop_assert_eq!(
                two_ok, straight_ok,
                "if-join verdict must equal its lub's: a={} b={} lub={}", a, b, lub
            );
            // And the ground truth: accepted iff the merged taint is @Public (index 0), because a
            // @Public return sink accepts only @Public.
            prop_assert_eq!(
                two_ok, lub == 0,
                "accepted iff merged taint is @Public: a={} b={} lub={}", a, b, lub
            );
        }

        /// The MATCH join is the lub over arms (SC-T4). For arm taints a, b, the two-arm exhaustive
        /// `match ch { A => x = <a>, B => x = <b> }; return x` must accept iff `lub(a,b)` is @Public
        /// — the same law as `if`, quantified over the lattice. Catches the original last-arm-wins
        /// under-tainting AND any over-tainting fix.
        #[test]
        fn match_join_equals_lub(a in 0usize..3, b in 0usize..3) {
            let prog = format!(
                "module sigil;
                 enum Choice {{ A, B }}
                 fn f(i: i64 @Internal, s: i64 @Secret, ch: Choice) -> i64 {{
                     let mut x: i64 = 0;
                     match ch {{
                         Choice::A => {{ x = {}; }},
                         Choice::B => {{ x = {}; }},
                     }}
                     return x;
                 }}
",
                src(a), src(b)
            );
            let ok = compile_named_module("p_match.sigil", &prog).is_ok();
            let lub = a.max(b);
            prop_assert_eq!(
                ok, lub == 0,
                "match-join accepted iff lub is @Public: a={} b={} lub={}", a, b, lub
            );
        }

        /// The LOOP join preserves the ZERO-ITERATION path (SC-T3). For pre-loop taint p and
        /// body-assigned taint b, `x = <p>; while c {{ x = <b> }}; return x` must accept iff
        /// `lub(p,b)` is @Public: the body may not run (so `x` can be @p) OR may run (so `x` can be
        /// @b). The original bug saw only the body and reported @b, dropping @p when p > b — this
        /// pins that the pre-state is never lowered by the body.
        #[test]
        fn while_join_preserves_pre(p in 0usize..3, b in 0usize..3) {
            let prog = format!(
                "module sigil;
                 fn f(i: i64 @Internal, s: i64 @Secret, c: bool) -> i64 {{
                     let mut x: i64 = 0;
                     x = {};
                     while c {{ x = {}; }}
                     return x;
                 }}
",
                src(p), src(b)
            );
            let ok = compile_named_module("p_while.sigil", &prog).is_ok();
            let lub = p.max(b);
            prop_assert_eq!(
                ok, lub == 0,
                "while-join accepted iff lub(pre,body) is @Public: p={} b={} lub={}", p, b, lub
            );
        }
    }
}
