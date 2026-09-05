//! Precise closure rows × effect-handler threading (roadmap Phase 1's hidden consumer).
//!
//! `effect_desugar` selects its E-functions by `f.effects.effects.contains(&eff_id)` over
//! ALL `module.functions` — lifted closures included — and any non-threadable member
//! (closures are never threadable: `is_threadable` requires `ModuleFunction`) bails the
//! ENTIRE effect out of threading, leaving its performs to die at the E004 gate. Changing
//! where a closure's row comes from therefore shifts threading in both directions; these
//! tests pin each.

use sigil_test_utils::pipeline::compile_module_codes;

/// UN-POISONING. A pure closure defined inside the performer used to inherit the
/// performer's `{ Reader }` row, enter `e_funcs` as a non-threadable member, and bail
/// the whole effect — E004. With the row inferred from the (pure) body, the closure
/// stays out of `e_funcs` and the program threads clean.
///
/// EMPIRICALLY VERIFIED, not assumed: with the row source temporarily switched back to
/// the over-approximation (`tracker.current_effects`), this exact program produced
/// `["E004", "E004", "E004"]`; with inference it matches its closure-free baseline
/// (clean), so the delta is precisely the closure's row.
#[test]
fn pure_closure_in_performer_no_longer_poisons_threading() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule a;\n\
         effect Reader { fn get() -> i64; }\n\
         fn f() -> i64 ! { Reader } { let p = fn(x: i64) -> i64 { return x + 1; }; return perform Reader.get(); }\n\
         fn run() -> i64 { return handle f() { Reader.get() => resume 42 }; }\n",
    );
    assert!(
        codes.is_empty(),
        "a PURE closure inside the performer must not drag the effect out of threading; \
         got {codes:?}"
    );
}

/// The baseline the test above is measured against: the same program without the
/// closure threads clean. If THIS ever gates, the un-poisoning test's assertion is
/// measuring the wrong thing — fix this one first.
#[test]
fn threading_baseline_without_closure_is_clean() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule a;\n\
         effect Reader { fn get() -> i64; }\n\
         fn f() -> i64 ! { Reader } { return perform Reader.get(); }\n\
         fn run() -> i64 { return handle f() { Reader.get() => resume 42 }; }\n",
    );
    assert!(
        codes.is_empty(),
        "threading baseline must be clean; got {codes:?}"
    );
}

/// FAIL-CLOSED entry. A closure whose body calls the effectful `f()` now carries
/// `{ Reader }`, so the effect gains a non-threadable member and threading bails —
/// E004, never a miscompile. (Two mechanisms can fire here — the closure's row pulling
/// it into `e_funcs`, and the extra call to `f` breaking the statement-level call
/// accounting; both gate, which is the property this test pins. The synthesized
/// threading cannot represent a perform-channel through a closure, so gating is the
/// correct conservative outcome until it can.)
#[test]
fn effectful_closure_bails_threading_fail_closed() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule a;\n\
         effect Reader { fn get() -> i64; }\n\
         fn f() -> i64 ! { Reader } { return perform Reader.get(); }\n\
         fn g() -> i64 { let p = fn(x: i64) -> i64 { return f(); }; return 0; }\n\
         fn run() -> i64 { return handle f() { Reader.get() => resume 42 }; }\n",
    );
    assert!(
        codes.iter().any(|c| c == "E004"),
        "an effectful-row closure must gate threading (E004), never miscompile; got {codes:?}"
    );
}
