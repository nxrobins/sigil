//! The ROW-POSITION SHAPE CENSUS — the "this class never comes back" ratchet
//! from the Phase 4 post-merge sweep.
//!
//! THE CLASS: a `TypeExpr` shape whose effect row is SILENTLY LOST. The sweep
//! found the parser's slice branch dropping the element's entire structure
//! (`&[Fn(i64) -> i64 ! { E }]` degraded to a slice of the NOMINAL type `Fn`
//! — params, return, and row all gone before any validator ran), and the
//! resolver's ref-branch reconstruction independently doing the same. A typo'd
//! row name got no T069; a row VARIABLE was not classified effect-kinded (its
//! only occurrence was invisible), producing a confusing T150 at call sites.
//!
//! THE FENCE, two layers:
//!
//! 1. THIS CENSUS: every shape position that can syntactically carry an
//!    effect row appears below with a TYPO'D name (non-generic AND generic
//!    variants — they run different validation paths), asserting the expected
//!    diagnostics fire. A future shape that silently drops a row fails its
//!    census row. When you ADD a row-bearing shape to the grammar, add its
//!    census rows here.
//! 2. EXHAUSTIVE DESTRUCTURES in the row walkers (`ast::collect_type_row_names`,
//!    `validate_fn_type_effect_rows`, the validators' walks): each opens with a
//!    full-field `TypeExpr` destructure with NO `..`, so growing `TypeExpr`
//!    breaks their compilation until the new field is consciously handled.
//!
//! Also pinned here (sweep findings, verified against merged main):
//! - the METHOD call paths run `type_compatible` on args (T071), so TD-1's
//!   generic-path hole never extended to methods;
//! - `&Fn`/`&[Fn]` are hard T281 (previously: silent degradation, then
//!   downstream T066/T062 noise);
//! - operation-bearing effects through ANY HOF boundary (row-poly or not) are
//!   the pre-existing fail-closed E004 handler-threading limit — NOT a
//!   Phase 4 regression;
//! - a tuple-wrapped returned closure still carries its instantiated row.

use sigil_compiler::source::SourceFile;
use sigil_test_utils::pipeline::compile_module_codes;

struct CensusRow {
    label: &'static str,
    src: String,
    /// Every code in this list must be present in the compile output.
    expect: &'static [&'static str],
}

fn census() -> Vec<CensusRow> {
    let hdr = "#[ring(outer)]\nmodule app;\neffect Log;\nrecord Holder<T> { tag: i64 }\n";
    let mk = |label: &'static str, sig: &str, expect: &'static [&'static str]| CensusRow {
        label,
        src: format!("{hdr}{sig}\n"),
        expect,
    };
    vec![
        // ── Non-generic signatures (resolve_type → validate_fn_type_effect_rows / T281 gate) ──
        mk(
            "bare Fn param row",
            "fn f(g: Fn(i64) -> i64 ! { Bogus }) -> i64 { return 0; }",
            &["T069"],
        ),
        mk(
            "Fn under a generic arg",
            "fn f(h: Holder<Fn(i64) -> i64 ! { Bogus }>) -> i64 { return 0; }",
            &["T069"],
        ),
        mk(
            "Fn in a tuple param",
            "fn f(t: (Fn(i64) -> i64 ! { Bogus }, i64)) -> i64 { return 0; }",
            &["T069"],
        ),
        mk(
            "Fn in an array param",
            "fn f(a: [Fn(i64) -> i64 ! { Bogus }; 2]) -> i64 { return 0; }",
            &["T069"],
        ),
        mk(
            "Fn nested in a Fn param",
            "fn f(g: Fn(Fn(i64) -> i64 ! { Bogus }) -> i64) -> i64 { return 0; }",
            &["T069"],
        ),
        mk(
            "parenthesized return row",
            "fn f() -> (Fn(i64) -> i64 ! { Bogus }) { return f(); }",
            &["T069"],
        ),
        // The sweep's shapes: structure now PRESERVED (row visible → T069) and
        // the ref/slice-of-fn form itself gated (T281).
        mk(
            "slice-elem Fn row (the sweep's silent-drop shape)",
            "fn f(fs: &[Fn(i64) -> i64 ! { Bogus }]) -> i64 { return 0; }",
            &["T281", "T069"],
        ),
        mk(
            "ref-of-Fn row",
            "fn f(g: &Fn(i64) -> i64 ! { Bogus }) -> i64 { return 0; }",
            &["T281", "T069"],
        ),
        mk(
            "ref-of-tuple carrying a row",
            "fn f(t: &(Fn(i64) -> i64 ! { Bogus }, i64)) -> i64 { return 0; }",
            &["T281", "T069"],
        ),
        mk(
            "slice-of-tuple carrying a row",
            "fn f(ts: &[(Fn(i64) -> i64 ! { Bogus }, i64)]) -> i64 { return 0; }",
            &["T281", "T069"],
        ),
        // ── Generic signatures (validate_effect_row_params — a DIFFERENT path:
        //    generic sigs never reach resolve_type) ──
        mk(
            "GENERIC bare Fn param row",
            "fn f<T>(g: Fn(i64) -> i64 ! { Bogus }, x: T) -> i64 { return 0; }",
            &["T069"],
        ),
        mk(
            "GENERIC Fn under a generic arg",
            "fn f<T>(h: Holder<Fn(i64) -> i64 ! { Bogus }>, x: T) -> i64 { return 0; }",
            &["T069"],
        ),
        mk(
            "GENERIC tuple param row",
            "fn f<T>(t: (Fn(i64) -> i64 ! { Bogus }, i64), x: T) -> i64 { return 0; }",
            &["T069"],
        ),
        mk(
            "GENERIC array param row",
            "fn f<T>(a: [Fn(i64) -> i64 ! { Bogus }; 2], x: T) -> i64 { return 0; }",
            &["T069"],
        ),
        mk(
            "GENERIC return row",
            "fn f<T>(x: T) -> (Fn(i64) -> i64 ! { Bogus }) { return f(x); }",
            &["T069"],
        ),
        mk(
            "GENERIC slice-elem Fn row",
            "fn f<T>(fs: &[Fn(i64) -> i64 ! { Bogus }], x: T) -> i64 { return 0; }",
            &["T281", "T069"],
        ),
        mk(
            "GENERIC ref-of-Fn row",
            "fn f<T>(g: &Fn(i64) -> i64 ! { Bogus }, x: T) -> i64 { return 0; }",
            &["T281", "T069"],
        ),
    ]
}

/// Every row-bearing shape must DIAGNOSE a typo'd row name — no shape may
/// silently drop a row again.
#[test]
fn every_row_bearing_shape_diagnoses_a_typo() {
    let mut failures = Vec::new();
    for row in census() {
        let codes = compile_module_codes(&row.src);
        for expected in row.expect {
            if !codes.iter().any(|c| c == expected) {
                failures.push(format!(
                    "[{}] expected {expected}, got {codes:?}",
                    row.label
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "shape census rows lost their diagnostics (a row-bearing shape is \
         silently dropping annotations again):\n{}",
        failures.join("\n")
    );
}

/// The AST-preservation pin for the parser fix: the slice branch must keep the
/// element's structure. Before the sweep, `fn_type` was hardcoded `None` here
/// and the row below did not exist in the AST at all.
#[test]
fn slice_element_structure_survives_parsing() {
    let sf = SourceFile::new(
        "census.sigil".to_string(),
        "module t;\nfn f(fs: &[Fn(i64) -> i64 ! { Log }]) -> i64 { return 0; }\n".to_string(),
    );
    let (program, diags) =
        sigil_compiler::parser::parse_with_id(&sf, sigil_compiler::span::SourceId::SYNTHETIC);
    assert!(diags.is_empty(), "parse must succeed: {diags:?}");
    let sigil_compiler::ast::Item::FnDef(def) = &program.modules[0].items[0] else {
        panic!("expected FnDef");
    };
    let ty = &def.params[0].ty;
    assert!(
        matches!(ty.ref_kind, Some(sigil_compiler::ast::RefKind::Slice)),
        "slice marker must survive"
    );
    let ft = ty
        .fn_type
        .as_ref()
        .expect("slice element's fn_type must be PRESERVED (the sweep's parser fix)");
    assert_eq!(
        ft.effects.as_deref(),
        Some(&["Log".to_string()][..]),
        "the element's effect row must survive parsing"
    );
}

// ── Sweep pins: verified-closed shapes stay closed ──

/// TD-1 never extended to methods: a generic impl method's concrete-row Fn
/// param REJECTS an effectful closure (the method path runs type_compatible).
#[test]
fn generic_method_concrete_row_is_enforced() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         record BoxV<T> { v: i64 }\n\
         impl BoxV<T> { fn call_it(self: BoxV<T>, f: Fn(i64) -> i64 ! { }) -> i64 { return f(1); } }\n\
         fn caller() -> i64 { let b: BoxV<i64> = BoxV { v: 1 }; \
         return b.call_it(fn(x: i64) -> i64 { return logs(); }); }\n",
    );
    assert!(
        codes.iter().any(|c| c == "T071"),
        "the generic-method path must keep rejecting row-contravariance \
         violations; got {codes:?}"
    );
}

/// Same pin for the non-generic method path.
#[test]
fn nongeneric_method_concrete_row_is_enforced() {
    let codes = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         record Plain { v: i64 }\n\
         impl Plain { fn call_it(self: Plain, f: Fn(i64) -> i64 ! { }) -> i64 { return f(1); } }\n\
         fn caller() -> i64 { let b: Plain = Plain { v: 1 }; \
         return b.call_it(fn(x: i64) -> i64 { return logs(); }); }\n",
    );
    assert!(
        codes.iter().any(|c| c == "T071"),
        "the method path must keep rejecting row-contravariance violations; \
         got {codes:?}"
    );
}

/// A row VARIABLE under a ref/slice shape is E011 (not a binding position)
/// AND the shape itself is T281 — fail-closed on both axes, replacing the
/// pre-sweep behavior (silent-clean when unused, T150+T062 noise when used).
#[test]
fn row_variable_under_ref_or_slice_is_rejected_on_both_axes() {
    for sig in [
        "fn h<e>(fs: &[Fn(i64) -> i64 ! { e }]) -> i64 ! { e } { return 0; }",
        "fn h<e>(g: &Fn(i64) -> i64 ! { e }) -> i64 ! { e } { return 0; }",
    ] {
        let codes = compile_module_codes(&format!("#[ring(outer)]\nmodule app;\n{sig}\n"));
        assert!(
            codes.iter().any(|c| c == "T281") && codes.iter().any(|c| c == "E011"),
            "a row variable under a ref/slice must be T281 + E011; got {codes:?} for {sig}"
        );
    }
}

/// Operation-bearing effects through a HOF boundary are the PRE-EXISTING
/// fail-closed E004 handler-threading limit — pinned on both the row-poly
/// and the concrete-row shape so any future change here is deliberate
/// (either both start compiling, or both keep failing closed).
#[test]
fn operation_effect_through_hof_boundary_fails_closed_on_both_shapes() {
    let row_poly = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Reader { fn get() -> i64; }\n\
         fn h<e>(f: Fn(i64) -> i64 ! { e }) -> i64 ! { e } { return f(1); }\n\
         fn caller() -> i64 { \
         return handle h(fn(x: i64) -> i64 { return perform Reader.get(); }) { Reader.get() => 7 }; }\n",
    );
    let concrete = compile_module_codes(
        "#[ring(outer)]\nmodule app;\n\
         effect Reader { fn get() -> i64; }\n\
         fn h(f: Fn(i64) -> i64 ! { Reader }) -> i64 ! { Reader } { return f(1); }\n\
         fn caller() -> i64 { \
         return handle h(fn(x: i64) -> i64 { return perform Reader.get(); }) { Reader.get() => 7 }; }\n",
    );
    assert!(
        row_poly.iter().any(|c| c == "E004") && concrete.iter().any(|c| c == "E004"),
        "the handler-threading limit must stay fail-closed on BOTH shapes (or be \
         lifted for both, deliberately); got row_poly={row_poly:?} concrete={concrete:?}"
    );
}

/// A tuple-wrapped returned closure carries its instantiated row (the overlay
/// Tuple arm end-to-end): pure caller charged, declared caller clean.
#[test]
fn tuple_wrapped_returned_closure_carries_its_row() {
    let base = "#[ring(outer)]\nmodule app;\n\
         effect Log;\n\
         fn logs() -> i64 ! { Log } { return 0; }\n\
         fn mk<e>(f: Fn(i64) -> i64 ! { e }) -> (Fn(i64) -> i64 ! { e }, i64) { return (f, 0); }\n";
    let laundering = format!(
        "{base}fn pure_use() -> i64 {{ \
         let (g, n) = mk(fn(x: i64) -> i64 {{ return logs(); }}); return g(5); }}\n"
    );
    let codes = compile_module_codes(&laundering);
    assert!(
        codes.iter().any(|c| c == "E001"),
        "a tuple-wrapped returned closure must still discharge; got {codes:?}"
    );
    let declared = format!(
        "{base}fn ok_use() -> i64 ! {{ Log }} {{ \
         let (g, n) = mk(fn(x: i64) -> i64 {{ return logs(); }}); return g(5); }}\n"
    );
    let codes = compile_module_codes(&declared);
    assert!(
        codes.is_empty(),
        "the declared-row twin must stay clean; got {codes:?}"
    );
}
