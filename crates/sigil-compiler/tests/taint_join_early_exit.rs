//! Taint soundness across loop/match EARLY EXITS and lexical SHADOWS (docs/specs/taint-join-soundness.md).
//!
//! FOUND BY ADVERSARIAL VERIFICATION of the #252 control-flow-join fix (5 lenses + a completeness
//! critic, 93 probes). The example/property tests for the join shared the fix's blind spot; these
//! fixtures are the holes those tests missed. Three root causes:
//!
//!  1. **Early exit (`break`/`continue`) was modeled as a no-op**, so the checker kept traversing
//!     the statements AFTER the exit and applied their (taint-lowering) strong updates as if they
//!     ran on the exit path. A secret captured then `break`/`continue`d leaked past the reset. The
//!     fix captures the taint env at each `break`/`continue` and joins it into the loop EXIT / HEAD.
//!  2. **The loop fixpoint bound was a fixed 8**, too small for an N-link copy chain (needs ~N
//!     passes), panicking the compiler on long straight-line loop bodies. The bound is now sized to
//!     the binding count so convergence is guaranteed.
//!  3. **The flat `TaintEnv` conflated a lexically-shadowed inner `let`/pattern binding with an
//!     outer variable of the same name**, so the merge kept the (higher) shadow taint and rejected
//!     safe programs. Shadowed names are now restored to their outer binding at block/arm exit.
//!
//! Every rejection assertion pins the return/decl-sink message so a leak caught for an unrelated
//! reason does not count as a pass; every accept assertion guards against the shadow over-taint.

use sigil_compiler::CompileError;
use sigil_compiler::compile_named_module;

const T001_RETURN: &str = "returning @Secret value from function declared @Public";

fn err_debug(e: &CompileError) -> String {
    format!("{e:?}")
}

/// A program that leaks a secret to a @Public return MUST be rejected at the return sink.
fn assert_leak_rejected(name: &str, source: &str, why: &str) {
    match compile_named_module(name, source) {
        Ok(_) => panic!("SOUNDNESS HOLE: {why}\n--- source ---\n{source}"),
        Err(e) => {
            let d = err_debug(&e);
            assert!(
                d.contains(T001_RETURN),
                "rejected, but NOT at the return sink — not measuring the early-exit leak.\n\
                 wanted: {T001_RETURN:?}\ngot: {d}\n--- source ---\n{source}"
            );
        }
    }
}

/// A safe program (no real leak on any path) MUST compile — guards against the shadow over-taint.
fn assert_compiles(name: &str, source: &str, why: &str) {
    if let Err(e) = compile_named_module(name, source) {
        panic!(
            "FALSE REJECT: {why}\ngot: {}\n--- source ---\n{source}",
            err_debug(&e)
        );
    }
}

// ── Root cause 1: early exit (break / continue) across every loop construct ───────────────────────

#[test]
fn while_continue_skips_reset_is_rejected() {
    assert_leak_rejected(
        "ee_while_continue.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, c: bool, b: bool) -> i64 {
    let mut x: i64 = 0;
    while c {
        if b {
            x = s;
            continue;
        }
        x = 0;
    }
    return x;
}
"#,
        "continue skips the `x = 0` reset; x is @Secret at loop exit and leaks through the @Public return",
    );
}

#[test]
fn while_break_skips_reset_is_rejected() {
    assert_leak_rejected(
        "ee_while_break.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, c: bool, b: bool) -> i64 {
    let mut x: i64 = 0;
    while c {
        if b {
            x = s;
            break;
        }
        x = 0;
    }
    return x;
}
"#,
        "break exits with x=@Secret, skipping the trailing x=0; leaks through the @Public return",
    );
}

#[test]
fn for_range_break_dead_reset_is_rejected() {
    assert_leak_rejected(
        "ee_forrange_break.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, n: i64) -> i64 {
    let mut x: i64 = 0;
    for i in 0..n {
        x = s;
        break;
        x = 0;
    }
    return x;
}
"#,
        "for-range break leaves x=@Secret; the dead x=0 must not lower it",
    );
}

#[test]
fn for_range_continue_skips_reset_is_rejected() {
    assert_leak_rejected(
        "ee_forrange_continue.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, n: i64, b: bool) -> i64 {
    let mut x: i64 = 0;
    for i in 0..n {
        if b {
            x = s;
            continue;
        }
        x = 0;
    }
    return x;
}
"#,
        "for-range continue skips the reset; x can be @Secret at exit",
    );
}

#[test]
fn for_in_break_skips_reset_is_rejected() {
    assert_leak_rejected(
        "ee_forin_break.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, b: bool) -> i64 {
    let mut x: i64 = 0;
    for i in [1, 2, 3] {
        if b {
            x = s;
            break;
        }
        x = 0;
    }
    return x;
}
"#,
        "for-in break leaves x=@Secret; the ForIn fixpoint path shares the early-exit gap",
    );
}

#[test]
fn continue_inside_match_arm_in_loop_is_rejected() {
    assert_leak_rejected(
        "ee_match_continue.sigil",
        r#"module sigil;
enum Tag { A, B }
fn leak(s: i64 @Secret, c: bool, t: Tag) -> i64 {
    let mut x: i64 = 0;
    while c {
        match t {
            Tag::A => { x = s; continue; },
            Tag::B => { },
        }
        x = 0;
    }
    return x;
}
"#,
        "continue inside a match arm inside a loop skips the post-match reset",
    );
}

#[test]
fn break_reaches_let_downgrade_sink() {
    // Distinct SINK: the break-skip leak reaches a @Public let-decl downgrade, not just the return.
    match compile_named_module(
        "ee_break_let.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret, c: bool, b: bool) -> i64 {
    let mut x: i64 = 0;
    while c {
        if b {
            x = s;
            break;
        }
        x = 0;
    }
    let y: i64 @Public = x;
    return y;
}
"#,
    ) {
        Ok(_) => panic!("SOUNDNESS HOLE: break-skip leak reached the @Public let-downgrade sink"),
        Err(e) => {
            let d = err_debug(&e);
            assert!(
                d.contains("T001"),
                "must reject the @Secret→@Public let downgrade (T001). got: {d}"
            );
        }
    }
}

#[test]
fn break_bypasses_declassify_barrier() {
    // The break-skip leak launders the RAW secret past the authorized declassify barrier.
    let source = r#"module ext;
cap type Declassify {}
fn leak(s: i64 @Secret, d: Declassify, c: bool, b: bool) -> i64 @Public {
    let mut x: i64 = 0;
    while c {
        if b {
            x = s;
            break;
        }
        x = declassify(s, d);
    }
    return x;
}
"#;
    assert!(
        compile_named_module("ee_declassify.sigil", source).is_err(),
        "SOUNDNESS HOLE: break skipped the declassify barrier, leaking the RAW secret\n{source}"
    );
}

// ── Root cause 2: the fixpoint bound must scale with the copy-chain length (no panic) ──────────────

#[test]
fn long_copy_chain_loop_does_not_panic_and_rejects() {
    // A 12-link copy chain needs ~12 fixpoint passes; a fixed bound of 8 panicked. Must converge and
    // reject (the secret reaches `return a` through the chain).
    let source = r#"module sigil;
fn leak(s: i64 @Secret, c: bool) -> i64 {
    let mut a: i64 = 0;
    let mut b: i64 = 0;
    let mut d: i64 = 0;
    let mut e: i64 = 0;
    let mut f: i64 = 0;
    let mut g: i64 = 0;
    let mut h: i64 = 0;
    let mut j: i64 = 0;
    let mut k: i64 = 0;
    let mut m: i64 = 0;
    let mut n: i64 = 0;
    let mut p: i64 = 0;
    while c {
        a = b; b = d; d = e; e = f; f = g; g = h;
        h = j; j = k; k = m; m = n; n = p; p = s;
    }
    return a;
}
"#;
    // Must NOT panic (the assertion is that this returns Result, not unwinds) and must reject.
    assert_leak_rejected(
        "ee_chain.sigil",
        source,
        "a long copy chain propagates the secret to `return a`; the fixpoint must converge, not panic",
    );
}

// ── Root cause 3: lexical shadows must not conflate with an outer variable (no false reject) ───────

#[test]
fn match_arm_let_shadow_compiles() {
    assert_compiles(
        "ee_shadow_match.sigil",
        r#"module sigil;
enum Choice { A, B }
fn f(s: i64 @Secret, ch: Choice) -> i64 {
    let mut y: i64 = 0;
    match ch {
        Choice::A => { let y: i64 @Secret = s; },
        Choice::B => { y = 0; },
    }
    return y;
}
"#,
        "arm A's `let y` is a block-scoped shadow; the outer y is public on every path",
    );
}

#[test]
fn while_let_shadow_compiles() {
    assert_compiles(
        "ee_shadow_while.sigil",
        r#"module sigil;
fn f(s: i64 @Secret, c: bool) -> i64 {
    let mut y: i64 = 0;
    while c {
        y = 0;
        let y: i64 @Secret = s;
    }
    return y;
}
"#,
        "the loop body's `let y` is a scoped shadow dropped at body end; the outer y stays public",
    );
}

#[test]
fn for_range_let_shadow_compiles() {
    assert_compiles(
        "ee_shadow_for.sigil",
        r#"module sigil;
fn f(s: i64 @Secret, n: i64) -> i64 {
    let mut y: i64 = 0;
    for i in 0..n {
        y = 0;
        let y: i64 @Secret = s;
    }
    return y;
}
"#,
        "same scoped-shadow shape for the ForRange fixpoint body",
    );
}

#[test]
fn match_pattern_name_collision_compiles() {
    assert_compiles(
        "ee_pat_collision.sigil",
        r#"module sigil;
enum Opt { Some(i64), None }
fn f(opt: Opt @Secret) -> i64 {
    let mut x: i64 = 0;
    match opt {
        Opt::Some(x) => { },
        Opt::None => { },
    }
    return x;
}
"#,
        "the pattern-bound `x` (secret payload) is arm-scoped; `return x` is the outer public x",
    );
}

// ── Controls: the fixes must not RE-OPEN the join holes #252 already closed ────────────────────────

#[test]
fn plain_loop_secret_still_rejected() {
    // The original zero-iteration hole must still reject after the early-exit/shadow work.
    assert_leak_rejected(
        "ee_ctrl_while.sigil",
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
        "the zero-iteration path still leaves x @Secret",
    );
}

#[test]
fn safe_early_exit_loop_compiles() {
    // A loop with break/continue but NO secret must still compile.
    assert_compiles(
        "ee_ctrl_safe.sigil",
        r#"module sigil;
fn ok(a: i64, c: bool, b: bool) -> i64 {
    let mut x: i64 = 0;
    while c {
        if b {
            x = a;
            break;
        }
        x = 0;
    }
    return x;
}
"#,
        "break/continue with only public values must compile",
    );
}

// ── Divergence must be EXCLUDED from the merge (found by adversarial re-verification) ─────────────
//
// A branch/arm that diverges (return/break/continue) does not fall through to the code after the
// construct, so its bindings snapshot must NOT be lubbed into the merge — else the ubiquitous
// guard-clause pattern over-taints the falling-through path with the diverging branch's stale value.

/// `if c { return } else { x = <public> }; use(x)` — the then-branch diverges, so only the else path
/// reaches the merge, where x is provably @Public. MUST compile.
#[test]
fn if_divergent_guard_clause_compiles() {
    assert_compiles(
        "ee_div_if.sigil",
        r#"module sigil;
fn f(s: i64 @Secret, c: bool) -> i64 {
    let mut x: i64 = 0;
    x = s;
    if c {
        return 0;
    } else {
        x = 0;
    }
    return x;
}
"#,
        "the diverging then-branch (return) must not be merged; x is @Public on the only live path",
    );
}

/// A match where one arm returns and the other lowers x — only the falling-through arm reaches the
/// merge, so x is @Public. MUST compile.
#[test]
fn match_divergent_arm_compiles() {
    assert_compiles(
        "ee_div_match.sigil",
        r#"module sigil;
enum Choice { A, B }
fn f(s: i64 @Secret, e: Choice) -> i64 {
    let mut x: i64 = 0;
    x = s;
    match e {
        Choice::A => { return 0; },
        Choice::B => { x = 0; },
    }
    return x;
}
"#,
        "the diverging arm A (return) must not be merged; arm B lowers x to @Public",
    );
}

/// A loop body that lowers the outer `y`, then `let`-shadows it @Secret, then breaks — the break's
/// captured env must reflect the OUTER (public) y, not the arm-scoped shadow. MUST compile.
#[test]
fn shadow_captured_by_break_compiles() {
    assert_compiles(
        "ee_shadow_break.sigil",
        r#"module sigil;
fn f(s: i64 @Secret, c: bool) -> i64 {
    let mut y: i64 = 0;
    while c {
        y = 0;
        let y: i64 @Secret = s;
        break;
    }
    return y;
}
"#,
        "the shadow `let y = s` is out of scope at the break's exit target; outer y stays @Public",
    );
}

// ── Collision-shadow across MORE channels (found by a third adversarial round; all false-rejects) ──
//
// A name bound in a body/arm scope (a match PATTERN or a loop VARIABLE) that COLLIDES with an outer
// variable, then flows out via an early exit or the loop var itself, must not over-taint the outer
// variable. These are the pattern/loop-var siblings of the `let`-shadow-in-collectors fix. All are
// over-taints (never leaks — the pre floor keeps the accept direction sound).

#[test]
fn match_pattern_collision_break_compiles() {
    assert_compiles(
        "ee_pat_break.sigil",
        r#"module sigil;
enum Opt { Some(i64), None }
fn f(opt: Opt @Secret, c: bool) -> i64 {
    let mut x: i64 = 0;
    while c {
        match opt {
            Opt::Some(x) => { break; },
            Opt::None => { break; },
        }
    }
    return x;
}
"#,
        "the pattern-bound `x` (secret payload) is arm-scoped; either arm breaks, so the collector must restore the outer x",
    );
}

#[test]
fn match_pattern_collision_continue_compiles() {
    assert_compiles(
        "ee_pat_cont.sigil",
        r#"module sigil;
enum Opt { Some(i64), None }
fn f(opt: Opt @Secret, c: bool) -> i64 {
    let mut x: i64 = 0;
    while c {
        match opt {
            Opt::Some(x) => { break; },
            Opt::None => { continue; },
        }
    }
    return x;
}
"#,
        "same pattern-collision shape reaching the continue collector",
    );
}

#[test]
fn for_range_loop_var_collision_compiles() {
    assert_compiles(
        "ee_loopvar_range.sigil",
        r#"module sigil;
fn f(s: i64 @Secret, n: i64) -> i64 {
    let mut x: i64 = 0;
    for x in 0..n {
        x = s;
    }
    return x;
}
"#,
        "the range loop var `x` shadows the outer x over the body; the outer x is never written",
    );
}

#[test]
fn for_in_loop_var_collision_compiles() {
    assert_compiles(
        "ee_loopvar_forin.sigil",
        r#"module sigil;
fn f(s: i64 @Secret, arr: [i64; 4]) -> i64 {
    let mut x: i64 = 0;
    for x in arr {
        x = s;
    }
    return x;
}
"#,
        "the for-in element var `x` is body-scoped; the outer x stays @Public",
    );
}

// ── Implicit flow through secret-guarded control ────────────────────────────────────────────────
//
// These leak a PUBLIC value that is control-DEPENDENT on a secret — no secret VALUE is ever assigned
// (x only ever holds public constants). These were out of scope for #252's DATA-flow join and now
// serve as active regression canaries. `continuation_taint` preserves the controlling label after
// a one-sided early exit,
// and match guards join their label into both the guarded arm and subsequent-arm selection.

/// A secret-guarded `break` controls the loop trip count; the trailing public assignment records it.
/// `x` is only ever assigned public constants, yet `return x` reveals `s > 0` without continuation
/// taint propagation.
#[test]
fn implicit_flow_secret_guarded_break_leak() {
    assert_leak_rejected(
        "ee_impl_break.sigil",
        r#"module sigil;
fn leak(s: i64 @Secret) -> i64 {
    let mut x: i64 = 0;
    for i in 0..10 {
        if s > 0 { break; }
        x = 1;
    }
    return x;
}
"#,
        "secret-guarded break controls whether the public x = 1 runs — continuation pc must stay secret",
    );
}

/// A secret match GUARD selects which arm runs; the arm bodies assign only public constants, yet the
/// merged result reveals the guard. The If path raises pc by its condition; the match-guard path
/// does not unless the guard label is folded into arm selection.
#[test]
fn implicit_flow_secret_match_guard_leak() {
    assert_leak_rejected(
        "ee_impl_guard.sigil",
        r#"module sigil;
enum Choice { A, B }
fn leak(s: i64 @Secret, ch: Choice) -> i64 {
    let mut x: i64 = 0;
    match ch {
        Choice::A if s > 0 => { x = 1; },
        _ => { x = 0; },
    }
    return x;
}
"#,
        "a secret match guard selects the arm and must raise the arm-selection pc",
    );
}
