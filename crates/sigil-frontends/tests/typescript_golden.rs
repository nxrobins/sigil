//! FE0 TypeScript → SIGIL frontend tests. Structure mirrors the spec's test
//! plan: golden translation, round-trip validity, T199 enforcement, one
//! conformance assertion per existential constraint, determinism, and a
//! totality/fuzz pass. Goldens are hand-authored (threat T3), and the
//! round-trip + enforcement tests are independent correctness signals so the
//! suite is not tautological.

use std::path::PathBuf;

use proptest::prelude::*;

use sigil_compiler::{CompileOptions, compile_named_module, compile_named_module_with_options};
use sigil_frontends::{EmittedSigil, Frontend, FrontendDiag, codes, frontend_for, limits};

fn ts() -> Box<dyn Frontend> {
    frontend_for("typescript").expect("typescript frontend registered")
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/frontends/typescript")
}

fn norm(s: &str) -> String {
    s.replace("\r\n", "\n")
}

fn translate_ok(src: &str, name: &str) -> EmittedSigil {
    ts().translate(src, name)
        .unwrap_or_else(|d| panic!("translate `{name}` failed unexpectedly: {d:?}"))
}

fn translate_err(src: &str) -> Vec<FrontendDiag> {
    ts().translate(src, "t.ts")
        .expect_err("expected a translation error")
}

fn first_code(src: &str) -> &'static str {
    translate_err(src)
        .first()
        .expect("at least one diagnostic")
        .code
}

fn ts_files(sub: &str) -> Vec<PathBuf> {
    let dir = fixtures_dir().join(sub);
    let mut v: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {dir:?}: {e}"))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().and_then(|x| x.to_str()) == Some("ts"))
        .collect();
    v.sort();
    v
}

// ── 1. Golden translation (hand-authored goldens; threat T3) ────────────────
#[test]
fn golden_translation() {
    for p in ts_files("compile") {
        let src = std::fs::read_to_string(&p).unwrap();
        let golden_path = p.with_extension("sigil");
        let golden = std::fs::read_to_string(&golden_path)
            .unwrap_or_else(|_| panic!("missing golden {golden_path:?}"));
        let emitted = translate_ok(&src, p.to_str().unwrap());
        assert_eq!(
            norm(&emitted.text),
            norm(&golden),
            "golden mismatch for {p:?}"
        );
    }
}

// ── 2. Round-trip validity: every emitted golden compiles clean ─────────────
#[test]
fn round_trip_compiles() {
    for p in ts_files("compile") {
        let src = std::fs::read_to_string(&p).unwrap();
        let emitted = translate_ok(&src, p.to_str().unwrap());
        compile_named_module(emitted.source_name.clone(), emitted.text.clone()).unwrap_or_else(
            |e| {
                panic!(
                    "emitted SIGIL for {p:?} did not compile: {:?}",
                    e.diagnostics()
                )
            },
        );
    }
}

// ── 3/4. Enforcement: a stale cap is rejected with T199 by the COMPILER ──────
#[test]
fn enforce_stale_cap_is_t199() {
    let p = fixtures_dir().join("enforce_stale.ts");
    let src = std::fs::read_to_string(&p).unwrap();
    let emitted = translate_ok(&src, p.to_str().unwrap());

    // Without a build-deadline it is well-formed and compiles clean — proving
    // the rejection below is a policy fault, not emitter garbage (threat T10).
    compile_named_module(emitted.source_name.clone(), emitted.text.clone())
        .expect("fresh compile (no deadline) should succeed");

    // With a build-deadline past the cap's deadline (2020) → T199.
    let err = compile_named_module_with_options(
        emitted.source_name.clone(),
        emitted.text.clone(),
        CompileOptions {
            build_deadline: Some(2025),
        },
    )
    .expect_err("stale cap must be rejected at build time");
    assert!(
        err.diagnostics()
            .iter()
            .any(|d| d.message().contains("stale")),
        "expected a T199 stale-cap diagnostic, got: {:?}",
        err.diagnostics()
    );
}

// ── 5. Per-constraint conformance, driven by the committed reject fixtures ───
#[test]
fn reject_fixtures_match_expected_codes() {
    for p in ts_files("reject") {
        let src = std::fs::read_to_string(&p).unwrap();
        let want = src
            .lines()
            .find_map(|l| l.trim().strip_prefix("// expect-fe:"))
            .map(|s| s.trim().to_string())
            .unwrap_or_else(|| panic!("reject fixture {p:?} missing `// expect-fe:` header"));
        let got = first_code(&src);
        assert_eq!(got, want, "wrong FE-code for {p:?}");
    }
}

// ── 5b. Conformance cases without a dedicated fixture file ───────────────────
#[test]
fn conformance_inline() {
    // Threat T16: exponent / unsupported operators.
    assert_eq!(
        first_code("function f(a: number): number { return a ** 2; }"),
        codes::FE031_BAD_OPERATOR
    );
    // Threat T9: hex literal.
    assert_eq!(
        first_code("function f(a: number): number { return a + 0xff; }"),
        codes::FE030_BAD_NUMBER
    );
    // Threat T9: BigInt suffix.
    assert_eq!(
        first_code("function f(a: number): number { return a + 1n; }"),
        codes::FE030_BAD_NUMBER
    );
    // Threat T9 (review gap): a leading-zero deadline in @cap must be rejected
    // just like a leading-zero expression literal.
    assert_eq!(
        first_code("/** @cap C(deadline=0123) */\nfunction f(a: number): number { return a; }"),
        codes::FE030_BAD_NUMBER
    );
    // Threat T8: an emitted identifier may not use the synthetic prefix.
    assert_eq!(
        first_code("function f(a: number): number { return __fe_x; }"),
        codes::FE021_RESERVED_NAME
    );
    // Threat T7: identifier longer than 64 bytes.
    let long = "a".repeat(65);
    assert_eq!(
        first_code(&format!(
            "function {long}(a: number): number {{ return a; }}"
        )),
        codes::FE020_BAD_IDENTIFIER
    );
    // FE2: a `string` param type is out-of-subset (FE320); an unknown
    // identifier is an unresolved reference (FE308).
    assert_eq!(
        first_code("function f(a: string): number { return 0; }"),
        codes::FE320_UNSUPPORTED_TS
    );
    assert_eq!(
        first_code("function f(a: number): number { return b; }"),
        codes::FE308_UNRESOLVED_REFERENCE
    );
    // Review (FE030): a negative @cap deadline is unemittable as a SIGIL
    // parametric-cap literal; the i64::MIN magnitude is the overflow variant.
    // Both must be a clean policy reject, never an FE500 internal abort.
    assert_eq!(
        first_code("/** @cap C(deadline=-1) */\nfunction f(a: number): number { return a; }"),
        codes::FE030_BAD_NUMBER
    );
    assert_eq!(
        first_code(
            "/** @cap C(deadline=-9223372036854775808) */\nfunction f(a: number): number { return a; }"
        ),
        codes::FE030_BAD_NUMBER
    );
    // Review (FE320): a SIGIL primitive used as a bare type annotation (TS should
    // write `number`); the compiler would resolve it to the built-in, not a
    // record. (An *interface* named a primitive is FE021 — see the fixture.)
    assert_eq!(
        first_code("function f(p: i64): number { return 0; }"),
        codes::FE320_UNSUPPORTED_TS
    );
}

// Review (B): the emitted module name must satisfy the compiler's
// `^[a-z_][a-z0-9_]*$` (N011) — a name-resolution rule the FE500 parse
// self-check cannot see. A capitalized source-file name must lowercase to a
// compiler-valid module; a stem that collides with a keyword after lowercasing
// (`Type` → `type`) falls back deterministically to `policy`.
#[test]
fn module_name_is_lowercased_and_compiler_valid() {
    let src = "function Handler(a: number): number { return a; }";
    let emitted = translate_ok(src, "Policy.ts");
    assert!(
        emitted.text.contains("module policy;"),
        "module name must be lowercased; got:\n{}",
        emitted.text
    );
    // The trust anchor must ACCEPT the emitted SIGIL (no N011) — translate alone
    // only runs the parse self-check, which never sees name-resolution codes.
    compile_named_module(emitted.source_name.clone(), emitted.text.clone())
        .expect("emitted SIGIL with a lowercased module name must compile (no N011)");

    let kw = translate_ok(src, "Type.ts");
    assert!(
        kw.text.contains("module policy;"),
        "a keyword-after-lowercasing stem must fall back to `policy`; got:\n{}",
        kw.text
    );
}

// ── 6. Determinism (threat T6): identical input → byte-identical output ──────
#[test]
fn deterministic_emission() {
    let src = "/** @cap Net(deadline=2030) */\n\
               function f(a: number, b: number): number { return a + b * 2; }";
    let a = translate_ok(src, "x.ts").text;
    let b = translate_ok(src, "x.ts").text;
    assert_eq!(a, b);
}

// ── 7a. Depth cap: deep nesting fails fast with FE002, no stack overflow ─────
#[test]
fn depth_cap_rejects_without_overflow() {
    let mut e = String::from("a");
    for _ in 0..200 {
        e = format!("({e})");
    }
    let src = format!("function f(a: number): number {{ return {e}; }}");
    assert_eq!(first_code(&src), codes::FE002_TOO_LARGE);
}

// The depth guard lives in parse_factor, so it must also bound recursion that
// re-enters via the call-argument path (review T12), not just parentheses.
#[test]
fn depth_cap_covers_nested_calls() {
    let mut e = String::from("a");
    for _ in 0..200 {
        e = format!("f({e})");
    }
    let src = format!("function f(a: number): number {{ return {e}; }}");
    assert_eq!(first_code(&src), codes::FE002_TOO_LARGE);
}

// ── 7c. Totality, second axis: STATEMENT nesting and FLAT operator/postfix
// chains must ALSO reject (FE002) without a stack overflow. The expression depth
// guard in `parse_unary` alone left the statement path (nested `if`, `else if`
// chains, `while`) and flat chains (`a+a+…`, `a==a==…`, `a.f.f…`, `a*a*…`) —
// which parse in a LOOP at constant recursion depth but build an N-deep AST that
// overflows the downstream desugar/check/emit walkers AND the recursive `Drop` —
// unbounded, so adversarial nesting aborted the process (SIGABRT). Mirrors the
// Solidity frontend's `statement_and_unary_nesting_reject_without_overflow`.
#[test]
fn statement_and_flat_nesting_reject_without_overflow() {
    let n = 5000;
    let opens = "if (a > 0) { ".repeat(n);
    let closes = "} ".repeat(n);
    let nested_if = format!("function f(a: number): number {{ {opens}{closes}return a; }}");

    let elifs = "else if (a > 0) { return 1; } ".repeat(n);
    let else_if = format!(
        "function f(a: number): number {{ if (a > 0) {{ return 1; }} {elifs}else {{ return 0; }} }}"
    );

    let wopens = "while (a > 0) { ".repeat(n);
    let nested_while = format!("function f(a: number): number {{ {wopens}{closes}return a; }}");

    let flat_add = format!(
        "function f(a: number): number {{ return a{}; }}",
        " + a".repeat(n)
    );
    let flat_mul = format!(
        "function f(a: number): number {{ return a{}; }}",
        " * a".repeat(n)
    );
    let flat_eq = format!(
        "function f(a: number): boolean {{ return a{}; }}",
        " == a".repeat(n)
    );
    let flat_rel = format!(
        "function f(a: number): boolean {{ return a{}; }}",
        " < a".repeat(n)
    );
    let flat_field = format!(
        "function f(a: number): number {{ return a{}; }}",
        ".f".repeat(n)
    );
    let unary = format!(
        "function f(a: boolean): boolean {{ return {}a; }}",
        "!".repeat(n)
    );

    for (label, src) in [
        ("nested_if", nested_if),
        ("else_if", else_if),
        ("nested_while", nested_while),
        ("flat_add", flat_add),
        ("flat_mul", flat_mul),
        ("flat_eq", flat_eq),
        ("flat_rel", flat_rel),
        ("flat_field", flat_field),
        ("unary", unary),
    ] {
        assert_eq!(
            first_code(&src),
            codes::FE002_TOO_LARGE,
            "{label}: expected FE002, must reject deep nesting without overflowing"
        );
    }
}

// Property (threat T12): for ANY statement-nesting depth or flat-chain length,
// `translate` terminates with a clean Ok/Err — never a stack-overflow abort — and
// anything comfortably past `MAX_DEPTH` is rejected specifically by FE002 (the
// depth guard), not by an unrelated error masking a near-overflow.
proptest! {
    #[test]
    fn deep_nesting_is_bounded(n in 0usize..300, kind in 0u8..4) {
        let src = match kind {
            0 => {
                let o = "if (a > 0) { ".repeat(n);
                let c = "} ".repeat(n);
                format!("function f(a: number): number {{ {o}{c}return a; }}")
            }
            1 => format!("function f(a: number): number {{ return a{}; }}", " + a".repeat(n)),
            2 => format!("function f(a: number): number {{ return a{}; }}", ".f".repeat(n)),
            _ => format!("function f(a: boolean): boolean {{ return {}a; }}", "!".repeat(n)),
        };
        match ts().translate(&src, "p.ts") {
            // If it translated, the nesting was within the bound.
            Ok(_) => prop_assert!(n <= limits::MAX_DEPTH as usize),
            // Comfortably-over-bound inputs must be rejected by the depth guard itself.
            Err(d) => {
                if n > 2 * limits::MAX_DEPTH as usize {
                    prop_assert_eq!(d[0].code, codes::FE002_TOO_LARGE);
                }
            }
        }
    }
}

// ── 7b. Totality (threat T12): never panics on arbitrary input ──────────────
proptest! {
    #[test]
    fn never_panics_on_arbitrary_input(s in ".{0,400}") {
        // Ok or Err are both acceptable; the contract is "no panic / no hang".
        let _ = ts().translate(&s, "fuzz.ts");
    }

    #[test]
    fn never_panics_on_tokenish_input(
        s in proptest::collection::vec(
            prop::sample::select(vec![
                "function", " ", "(", ")", "{", "}", ":", ";", ",", "number",
                "return", "+", "-", "*", "/", "a", "1", "=>", "/**", "*/", "@cap",
                "@effects", "deadline", "=", "2030", "**", "\n",
            ]),
            0..40,
        ).prop_map(|v| v.join(" "))
    ) {
        let _ = ts().translate(&s, "fuzz.ts");
    }
}

// ── FE1: @effects (outer-ring effect contracts) ─────────────────────────────

// Enforcement: a function omitting an effect its callee declares → the COMPILER
// emits E001 (the FE1 analog of FE0's T199 demo).
#[test]
fn enforce_effect_leak_is_e001() {
    let p = fixtures_dir().join("enforce_leak.ts");
    let src = std::fs::read_to_string(&p).unwrap();
    let emitted = translate_ok(&src, p.to_str().unwrap());
    let err = compile_named_module(emitted.source_name.clone(), emitted.text.clone())
        .expect_err("effect leakage must be rejected at compile time");
    assert!(
        err.diagnostics()
            .iter()
            .any(|d| d.message().contains("undeclared effect")),
        "expected an E001 effect-leakage diagnostic, got: {:?}",
        err.diagnostics()
    );
}

#[test]
fn conformance_effect_mode() {
    // F8: an empty `@effects` still selects effect-mode (outer ring).
    let e = translate_ok(
        "/** @effects */\nfunction f(a: number): number { return a; }",
        "m.ts",
    );
    assert!(
        e.text.contains("#[ring(outer)]"),
        "empty @effects must select effect-mode; got: {}",
        e.text
    );
    // F7/FE211: an effect name colliding with a function name.
    assert_eq!(
        first_code("/** @effects fetch */\nfunction fetch(a: number): number { return a; }"),
        codes::FE211_NAME_COLLISION
    );
    // F1/FE201: a file mixing @cap and @effects.
    assert_eq!(
        first_code(
            "/** @cap C(deadline=1) */\nfunction a(x: number): number { return x; }\n\
             /** @effects NetIO */\nfunction b(x: number): number { return x; }"
        ),
        codes::FE201_MIXED_MODE
    );
    // F11/FE213: a compiler-reserved effect name.
    assert_eq!(
        first_code("/** @effects Alloc */\nfunction f(a: number): number { return a; }"),
        codes::FE213_RESERVED_EFFECT
    );
}

// F4: effects given out of order must emit sorted and byte-stable.
#[test]
fn deterministic_effect_emission() {
    let src = "/** @effects NetIO, FsIO, Crypto */\n\
               function f(a: number): number { return a; }";
    let a = translate_ok(src, "m.ts").text;
    let b = translate_ok(src, "m.ts").text;
    assert_eq!(a, b, "translation must be byte-stable");
    assert!(
        a.contains("! { Crypto, FsIO, NetIO }"),
        "effect row must be lexicographically sorted; got: {a}"
    );
}

// ── Adversarial mode-ring tests (dimension F1/F6/F12) ─────────────────────

#[test]
fn adv_effect_only_mode() {
    // A single @effects function → effect-mode (outer ring)
    let result = translate_ok(
        "/** @effects NetIO */\nfunction f(a: number): number { return a; }",
        "t.ts",
    );
    assert!(
        result.text.contains("#[ring(outer)]"),
        "effect-only must emit #[ring(outer)]"
    );
    assert!(
        !result.text.contains("cap type"),
        "effect-only must not emit cap types"
    );
}

#[test]
fn adv_cap_only_mode() {
    // A single @cap function → cap-mode (inner ring, no ring attr)
    let result = translate_ok(
        "/** @cap Net(deadline=2030) */\nfunction f(a: number): number { return a; }",
        "t.ts",
    );
    assert!(
        !result.text.contains("#[ring(outer)]"),
        "cap-only must not emit #[ring(outer)]"
    );
    assert!(
        result.text.contains("cap type"),
        "cap-only must emit cap types"
    );
}

#[test]
fn adv_neither_annotation_is_cap_mode() {
    // No @cap and no @effects → cap-mode (inner ring)
    let result = translate_ok("function f(a: number): number { return a; }", "t.ts");
    assert!(
        !result.text.contains("#[ring(outer)]"),
        "neither-annotation must not emit #[ring(outer)]"
    );
    assert!(
        !result.text.contains("cap type"),
        "neither-annotation with no caps must not emit cap types"
    );
}

#[test]
fn adv_cap_then_neither_is_cap_mode() {
    // One @cap function + one bare function → cap-mode
    let result = translate_ok(
        "/** @cap Net(deadline=2030) */\nfunction a(x: number): number { return x; }\n\
         function b(x: number): number { return x; }",
        "t.ts",
    );
    assert!(
        !result.text.contains("#[ring(outer)]"),
        "cap+neither must be cap-mode"
    );
    assert!(
        result.text.contains("cap type Net"),
        "cap+neither must emit cap type"
    );
}

#[test]
fn adv_effect_then_neither_is_effect_mode() {
    // One @effects function + one bare function → effect-mode
    let result = translate_ok(
        "/** @effects NetIO */\nfunction a(x: number): number { return x; }\n\
         function b(x: number): number { return x; }",
        "t.ts",
    );
    assert!(
        result.text.contains("#[ring(outer)]"),
        "effect+neither must be effect-mode"
    );
    assert!(
        result.text.contains("effect NetIO;"),
        "effect+neither must emit effect decl"
    );
}

#[test]
fn adv_multiple_caps_is_cap_mode() {
    // Multiple @cap functions → cap-mode
    let result = translate_ok(
        "/** @cap Net(deadline=2030) */\nfunction a(x: number): number { return x; }\n\
         /** @cap File(deadline=2040) */\nfunction b(x: number): number { return x; }",
        "t.ts",
    );
    assert!(
        !result.text.contains("#[ring(outer)]"),
        "multi-cap must be cap-mode"
    );
    assert!(
        result.text.contains("cap type Net"),
        "multi-cap must emit both cap types"
    );
    assert!(
        result.text.contains("cap type File"),
        "multi-cap must emit both cap types"
    );
}

#[test]
fn adv_multiple_effects_is_effect_mode() {
    // Multiple @effects functions → effect-mode
    let result = translate_ok(
        "/** @effects NetIO */\nfunction a(x: number): number { return x; }\n\
         /** @effects FsIO */\nfunction b(x: number): number { return x; }",
        "t.ts",
    );
    assert!(
        result.text.contains("#[ring(outer)]"),
        "multi-effect must be effect-mode"
    );
    assert!(
        result.text.contains("effect NetIO;"),
        "multi-effect must emit effect decls"
    );
    assert!(
        result.text.contains("effect FsIO;"),
        "multi-effect must emit effect decls"
    );
}

// ── FE2 gates (M1/M2 soundness, M6 determinism) ─────────────────────────────

// M1/M2: every input the checker ACCEPTS must compile with ZERO compiler errors
// — the translator's sound checker, not the oracle, is what rejects ill-typed
// programs (no T-code masquerade). A broad matrix witnesses the universal
// property: if the checker were unsound, one of these would emit a T-code.
#[test]
fn accepted_inputs_emit_zero_tcode_sigil() {
    let snippets = [
        "function a(x: number, y: number): boolean { return x < y; }",
        "function a(x: number, y: number): boolean { return x <= y; }",
        "function a(x: number, y: number): boolean { return x > y; }",
        "function a(x: number, y: number): boolean { return x >= y; }",
        "function a(x: number, y: number): boolean { return x == y; }",
        "function a(x: number, y: number): boolean { return x != y; }",
        "function a(x: boolean, y: boolean): boolean { return x == y; }",
        "function a(x: number): number { return -x; }",
        "function a(x: boolean): boolean { return !x; }",
        "function a(x: number, y: number): number { return x + y * 2 - 1; }",
        "function a(p: boolean, q: boolean): boolean { return p && q || !p; }",
        "interface P { x: number; y: boolean } function m(a: number): P { return { x: a, y: true }; }",
        "interface P { x: number } function g(p: P): number { return p.x; }",
        "function c(x: number): number { let r = x; if (x < 0) { r = 0; } else {} return r; }",
        "function w(n: number): number { let s = 0; let i = 0; while (i < n) { s = s + i; i = i + 1; } return s; }",
    ];
    for s in snippets {
        let emitted = translate_ok(s, "g.ts");
        compile_named_module(emitted.source_name.clone(), emitted.text.clone()).unwrap_or_else(
            |e| {
                panic!(
                    "accepted input emitted T-coded SIGIL:\n{s}\n--- emitted ---\n{}\n--- diags ---\n{:?}",
                    emitted.text,
                    e.diagnostics()
                )
            },
        );
    }
}

// M6: construction fields are canonicalized to declaration order, byte-stable.
#[test]
fn construction_field_order_is_canonical() {
    let src = "interface P { a: number; b: number }\n\
               function m(x: number, y: number): P { return { b: y, a: x }; }";
    let a = translate_ok(src, "m.ts").text;
    let b = translate_ok(src, "m.ts").text;
    assert_eq!(a, b, "translation must be byte-stable");
    assert!(
        a.contains("P { a: x, b: y }"),
        "construction fields must be in declaration order; got: {a}"
    );
}

// Finding-3 / M6 guard: record-construction fields are ALWAYS emitted in interface
// DECLARATION order, regardless of the order written in the object literal. This is
// the correctness/determinism invariant that the O(N)-lookup refactor of the field
// matching (check.rs `declared_ty` map + emit.rs `provided` map) must preserve.
proptest! {
    #[test]
    fn record_construction_emits_in_declaration_order(keys in prop::collection::vec(any::<u16>(), 6)) {
        // Fields f0..f5 declared in order; the object literal is a permutation, sorted by `keys`.
        let mut order: Vec<usize> = (0..6).collect();
        order.sort_by_key(|&i| keys[i]);
        let decl = (0..6).map(|i| format!("f{i}: number;")).collect::<Vec<_>>().join(" ");
        let ctor = order.iter().map(|&i| format!("f{i}: {i}")).collect::<Vec<_>>().join(", ");
        let src = format!("interface R {{ {decl} }}\nfunction m(): R {{ return {{ {ctor} }}; }}");
        let e = ts().translate(&src, "r.ts").expect("in-subset record must translate");
        // The construction must list fields in DECLARATION order: `f0: 0, f1: 1, … f5: 5`.
        let expected = (0..6).map(|i| format!("f{i}: {i}")).collect::<Vec<_>>().join(", ");
        prop_assert!(
            e.text.contains(&expected),
            "fields must emit in declaration order `{expected}`, got:\n{}",
            e.text
        );
    }
}
