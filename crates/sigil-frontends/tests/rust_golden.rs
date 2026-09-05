//! RS0 Rust → SIGIL frontend tests. Mirrors the TypeScript/Solidity suites:
//! golden translation, round-trip validity (every emitted golden compiles clean),
//! one conformance assertion per reject fixture, an accepted-inputs matrix that
//! witnesses oracle agreement (SC-7: an accepted input never emits a T-code), a
//! positive-floor guard (SC-6), determinism, and a totality/depth pass (SC-8).

use std::path::PathBuf;

use proptest::prelude::*;

use sigil_compiler::{CompileOptions, compile_named_module, compile_named_module_with_options};
use sigil_frontends::{EmittedSigil, Frontend, FrontendDiag, codes, frontend_for};

fn rs() -> Box<dyn Frontend> {
    frontend_for("rust").expect("rust frontend registered")
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/frontends/rust")
}

fn norm(s: &str) -> String {
    s.replace("\r\n", "\n")
}

fn translate_ok(src: &str, name: &str) -> EmittedSigil {
    rs().translate(src, name)
        .unwrap_or_else(|d| panic!("translate `{name}` failed unexpectedly: {d:?}"))
}

fn translate_err(src: &str) -> Vec<FrontendDiag> {
    rs().translate(src, "t.rs")
        .expect_err("expected a translation error")
}

fn first_code(src: &str) -> &'static str {
    translate_err(src)
        .first()
        .expect("at least one diagnostic")
        .code
}

fn rs_files(sub: &str) -> Vec<PathBuf> {
    let dir = fixtures_dir().join(sub);
    let mut v: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {dir:?}: {e}"))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().and_then(|x| x.to_str()) == Some("rs"))
        .collect();
    v.sort();
    v
}

// ── 1. Golden translation (hand-authored goldens) ───────────────────────────
#[test]
fn golden_translation() {
    for p in rs_files("compile") {
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
    for p in rs_files("compile") {
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

// ── RS1 enforcement: a stale cap is rejected with T199 by the COMPILER ───────
// The FE0 analog: the translator is untrusted, but SIGIL PROVES the cap contract.
#[test]
fn enforce_stale_cap_is_t199() {
    let p = fixtures_dir().join("enforce_stale.rs");
    let src = std::fs::read_to_string(&p).unwrap();
    let emitted = translate_ok(&src, p.to_str().unwrap());

    // Fresh (no build-deadline) compiles clean — proving the rejection below is a
    // policy fault, not emitter garbage.
    compile_named_module(emitted.source_name.clone(), emitted.text.clone())
        .expect("fresh compile (no deadline) should succeed");

    // With a build-deadline past the cap's deadline (2020) → T199 (stale cap).
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

// ── RS2 enforcement: an effect leak is rejected with E001 by the COMPILER ─────
// The FE1 analog: `handler` omits an effect its callee `fetch` declares.
#[test]
fn enforce_effect_leak_is_e001() {
    let p = fixtures_dir().join("enforce_leak.rs");
    let src = std::fs::read_to_string(&p).unwrap();
    let emitted = translate_ok(&src, p.to_str().unwrap());
    // `handler` (! { }) calls `fetch` (! { NetIO }) → the compiler emits E001.
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

// ── RS5a enforcement: an information-flow leak is rejected with T001 by the
// COMPILER. Unlike RS4a/b, taint checking is ALWAYS-ON (`taint_check::check_taints`
// runs unconditionally), so this fires on the DEFAULT feature set — the first
// enforce demo needing no `--features solver` lane. SR-T5/SR-T11: assert the exact
// code (verified by running the emitted program) + a genuine reject. ──────────────
#[test]
fn enforce_taint_leak_is_t001() {
    let p = fixtures_dir().join("enforce_taint_leak.rs");
    let src = std::fs::read_to_string(&p).unwrap();
    let emitted = translate_ok(&src, p.to_str().unwrap());
    // `leak(s: i64 @Secret) -> i64` returns @Secret where the default @Public return
    // is declared, with no `declassify` → the compiler emits T001.
    let err = compile_named_module(emitted.source_name.clone(), emitted.text.clone())
        .expect_err("an information-flow downgrade must be rejected at compile time");
    let diags = err.diagnostics();
    assert!(
        diags.iter().any(|d| d.code().as_str() == "T001"),
        "expected a T001 taint-downgrade diagnostic, got: {diags:?}"
    );
    assert!(
        !diags
            .iter()
            .any(|d| d.message().to_lowercase().contains("parse")),
        "the rejection must be a taint disproof, not a parse failure: {diags:?}"
    );

    // The Tier-A companion (`Secret → Secret`) compiles clean — proving the rejection
    // is a policy verdict, not emitter garbage (the enforce-stale structure).
    let g = fixtures_dir().join("compile/taint_upward.rs");
    let gsrc = std::fs::read_to_string(&g).unwrap();
    let gemit = translate_ok(&gsrc, g.to_str().unwrap());
    compile_named_module(gemit.source_name.clone(), gemit.text.clone())
        .expect("an upward (Secret->Secret) flow must satisfy the lattice and compile clean");
}

// ── RS5b enforcement: the `declassify` escape hatch turns the RS5a T001 leak
// CLEAN — and only for the declassified value. Both are DEFAULT-feature demos
// (taint + ownership are always-on), like RS5a. The frontend synthesizes the
// linear `Cap<Declassify>`; SIGIL proves the flow. ─────────────────────────────
#[test]
fn enforce_declassify_makes_leak_clean() {
    // The RS5a leak (`@Secret` param → default `@Public` return, no declassify) is
    // T001. Wrapping the returned value in `declassify(s)` authorizes the downgrade,
    // so the IDENTICAL shape compiles clean — the escape hatch working.
    let leak = "#[sigil::taint(s = Secret)]\npub fn reveal(s: i64) -> i64 { s }\n";
    let leak_em = translate_ok(leak, "reveal.rs");
    let leak_err = compile_named_module(leak_em.source_name.clone(), leak_em.text.clone())
        .expect_err("the un-declassified leak must be rejected (the RS5a T001 baseline)");
    assert!(
        leak_err
            .diagnostics()
            .iter()
            .any(|d| d.code().as_str() == "T001"),
        "expected T001 on the un-declassified leak, got: {:?}",
        leak_err.diagnostics()
    );

    let ok = "#[sigil::taint(s = Secret)]\npub fn reveal(s: i64) -> i64 { declassify(s) }\n";
    let ok_em = translate_ok(ok, "reveal.rs");
    compile_named_module(ok_em.source_name.clone(), ok_em.text.clone()).expect(
        "declassify authorizes the @Secret->@Public downgrade; the same shape must compile clean",
    );
}

#[test]
fn enforce_declassify_is_precise_t001() {
    // declassify launders ONLY its argument: `a` is declassified but the still-@Secret
    // `b` is returned → T001. Proves declassify is a targeted downgrade, not a blanket
    // laundromat — the trusted, always-on `taint_check` still guards the other secret.
    let p = fixtures_dir().join("enforce_declassify_precise.rs");
    let src = std::fs::read_to_string(&p).unwrap();
    let emitted = translate_ok(&src, p.to_str().unwrap());
    let err = compile_named_module(emitted.source_name.clone(), emitted.text.clone())
        .expect_err("declassifying `a` must not launder `b`; returning `b` is a leak");
    let diags = err.diagnostics();
    assert!(
        diags.iter().any(|d| d.code().as_str() == "T001"),
        "expected T001 (b is still @Secret), got: {diags:?}"
    );
    assert!(
        !diags
            .iter()
            .any(|d| d.message().to_lowercase().contains("parse")),
        "the rejection must be a taint disproof, not a parse failure: {diags:?}"
    );
}

// ── RS4a enforcement (solver-gated): an unprovable precondition → T211 ────────
// The money-shot: the translator emits `where x > 0` faithfully; the trusted
// compiler REFUTES the call `needs_pos(n)` with an UNGUARDED, non-literal `n` — the
// arg is symbolic with no preserved refinement (T211). (T224 is the sibling case:
// an arg that DOES carry a refinement, but one too weak to subsume `x > 0`.) SR-6 —
// the demo asserts the specific refinement-enforcement code and a genuine reject
// (not a parse-failure or a solver timeout), paired with the guarded companion
// compiling clean (the enforce-stale "fresh-clean / violation-rejected" structure).
#[cfg(feature = "solver")]
#[test]
fn enforce_unprovable_requires_is_t211() {
    let p = fixtures_dir().join("enforce_unprovable_requires.rs");
    let src = std::fs::read_to_string(&p).unwrap();
    let emitted = translate_ok(&src, p.to_str().unwrap());
    let err = compile_named_module(emitted.source_name.clone(), emitted.text.clone())
        .expect_err("an unprovable precondition must be rejected by the solver");
    let diags = err.diagnostics();
    assert!(
        diags.iter().any(|d| d.code().as_str() == "T211"),
        "expected a T211 symbolic-argument refinement violation, got: {diags:?}"
    );
    // SR-6: a genuine refinement rejection, not a solver timeout or a parse failure.
    assert!(
        !diags.iter().any(|d| {
            let m = d.message().to_lowercase();
            m.contains("timeout") || m.contains("parse")
        }),
        "the rejection must be a refinement disproof, not a timeout/parse failure: {diags:?}"
    );

    // The guarded companion compiles CLEAN under the same solver — proving the
    // rejection is a policy verdict, not emitter garbage.
    let g = fixtures_dir().join("compile/requires_guarded.rs");
    let gsrc = std::fs::read_to_string(&g).unwrap();
    let gemit = translate_ok(&gsrc, g.to_str().unwrap());
    compile_named_module(gemit.source_name.clone(), gemit.text.clone())
        .expect("the guarded call must discharge the precondition and compile clean");
}

// ── RS4b enforcement (solver-gated): a construction violating a struct invariant is
// refuted. `Range { lo: 10, hi: 5 }` breaks `where lo <= hi`, so the trusted compiler
// rejects it. Paired with the valid `range.rs` companion compiling clean. ───────────
#[cfg(feature = "solver")]
#[test]
fn enforce_bad_construction_is_refined() {
    let p = fixtures_dir().join("enforce_bad_range.rs");
    let src = std::fs::read_to_string(&p).unwrap();
    let emitted = translate_ok(&src, p.to_str().unwrap());
    let err = compile_named_module(emitted.source_name.clone(), emitted.text.clone())
        .expect_err("a construction violating the invariant must be rejected by the solver");
    let diags = err.diagnostics();
    // Construction-refinement violation → T210 (record-construction violates a
    // declared refinement). Assert the specific code + a genuine reject.
    assert!(
        diags.iter().any(|d| d.code().as_str() == "T210"),
        "expected a T210 refinement-violation at construction, got: {diags:?}"
    );
    assert!(
        !diags.iter().any(|d| {
            let m = d.message().to_lowercase();
            m.contains("timeout") || m.contains("parse")
        }),
        "the rejection must be a refinement disproof, not a timeout/parse failure: {diags:?}"
    );

    // The valid companion (`Range { lo: 0, hi: 1 }`) compiles clean under the solver.
    let g = fixtures_dir().join("compile/range.rs");
    let gsrc = std::fs::read_to_string(&g).unwrap();
    let gemit = translate_ok(&gsrc, g.to_str().unwrap());
    compile_named_module(gemit.source_name.clone(), gemit.text.clone())
        .expect("a valid construction must satisfy the invariant and compile clean");
}

// ── SR-5 (solver-gated): the frontend's emittable predicate fragment ⊆ SIGIL's
// Z3 fragment. Every accepted refinement fixture must compile CLEAN under
// `--features solver` (zero T-codes) — the refinement analog of SC-7's oracle
// agreement. A future Z3-fragment shrink turns this red instead of drifting. ────
#[cfg(feature = "solver")]
#[test]
fn refinement_fragment_is_z3_dischargeable() {
    let mut checked = 0;
    for p in rs_files("compile") {
        let src = std::fs::read_to_string(&p).unwrap();
        let emitted = translate_ok(&src, p.to_str().unwrap());
        // A fixture is refinement-bearing iff the emitted SIGIL has a `where` clause
        // (RS4a fn preconditions + RS4b record invariants). Non-refinement fixtures
        // discharge trivially and are covered by the plain round-trip.
        if !emitted.text.contains(" where ") {
            continue;
        }
        compile_named_module(emitted.source_name.clone(), emitted.text.clone()).unwrap_or_else(
            |e| {
                panic!(
                    "accepted refinement fixture {p:?} did not discharge under the solver: {:?}",
                    e.diagnostics()
                )
            },
        );
        checked += 1;
    }
    assert!(
        checked >= 4,
        "expected ≥4 refinement fixtures (RS4a + RS4b) to pin the fragment"
    );
}

// ── SC-6: a positive-floor guard — an empty accept-set is a failing suite ────
#[test]
fn positive_conformance_floor() {
    let n = rs_files("compile").len();
    assert!(
        n >= 4,
        "SC-6: the RS0 skeleton must keep a positive-floor of compile fixtures (found {n})"
    );
}

// ── 3. Per-constraint conformance, driven by the committed reject fixtures ───
#[test]
fn reject_fixtures_match_expected_codes() {
    for p in rs_files("reject") {
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

// ── 3b. Conformance cases without a dedicated fixture file ───────────────────
#[test]
fn conformance_inline() {
    // FE611: shift / bitwise operators.
    assert_eq!(
        first_code("pub fn f(a: i64) -> i64 { a << 2 }"),
        codes::FE611_BAD_OPERATOR_RS
    );
    // `::` now lexes as an enum-variant path (RS3b). A multi-segment path
    // (`a::b::c`) is still out-of-subset (FE601); a `Name::v(args)` shape is a
    // deferred payload construction (FE652).
    assert_eq!(
        first_code("pub fn f() -> i64 { a::b::c }"),
        codes::FE601_UNSUPPORTED_RS
    );
    assert_eq!(
        first_code("pub fn f() -> i64 { std::mem() }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE642: a method call `.f()` is out-of-subset (field access `.f` is in — RS3).
    assert_eq!(
        first_code("pub fn f(a: i64) -> i64 { a.count() }"),
        codes::FE642_BAD_FIELD_ACCESS_RS
    );
    // FE601: a program needs at least one function (a struct-only file is rejected).
    assert_eq!(
        first_code("struct S { x: i64 }"),
        codes::FE601_UNSUPPORTED_RS
    );
    // FE620: identifier over 64 bytes; and a non-ASCII identifier.
    let long = "a".repeat(65);
    assert_eq!(
        first_code(&format!("pub fn {long}() -> i64 {{ 0 }}")),
        codes::FE620_BAD_IDENTIFIER_RS
    );
    assert_eq!(
        first_code("pub fn café() -> i64 { 0 }"),
        codes::FE620_BAD_IDENTIFIER_RS
    );
    // FE620: a function name colliding with the `trap_if` builtin (SC-2).
    assert_eq!(
        first_code("pub fn trap_if(a: i64) -> i64 { a }"),
        codes::FE620_BAD_IDENTIFIER_RS
    );
    // FE630: arity mismatch, and a bool operand in arithmetic.
    assert_eq!(
        first_code("pub fn g(x: i64) -> i64 { x }\npub fn f() -> i64 { g(1, 2) }"),
        codes::FE630_ILL_TYPED_RS
    );
    assert_eq!(
        first_code("pub fn f(a: bool) -> i64 { a + 1 }"),
        codes::FE630_ILL_TYPED_RS
    );
    // FE634: a call to an undeclared function.
    assert_eq!(
        first_code("pub fn f(a: i64) -> i64 { g(a) }"),
        codes::FE634_UNRESOLVED_REFERENCE_RS
    );

    // ── increment 2: locals + control flow ──
    // FE633: reassigning a parameter (params are immutable in RS0).
    assert_eq!(
        first_code("pub fn f(a: i64) -> i64 { a = 1; return a; }"),
        codes::FE633_ILLEGAL_REASSIGNMENT_RS
    );
    // FE634: assignment to an unbound name.
    assert_eq!(
        first_code("pub fn f(a: i64) -> i64 { z = 1; return a; }"),
        codes::FE634_UNRESOLVED_REFERENCE_RS
    );
    // FE601: control-flow beyond if/while/match (`for`/`loop`) is deferred.
    assert_eq!(
        first_code("pub fn f(a: i64) -> i64 { for x in y { return 0; } return a; }"),
        codes::FE601_UNSUPPORTED_RS
    );
    // FE651: `match` is now supported (RS3b) — an empty match on `i64` is
    // non-exhaustive (needs a `_`), not an unsupported construct.
    assert_eq!(
        first_code("pub fn f(a: i64) -> i64 { match a { } }"),
        codes::FE651_NONEXHAUSTIVE_MATCH_RS
    );
    // FE630: a `while` condition that is not `bool` (no truthiness).
    assert_eq!(
        first_code("pub fn f(a: i64) -> i64 { while a { return 0; } return a; }"),
        codes::FE630_ILL_TYPED_RS
    );

    // ── RS1: capabilities ──
    // FE010: a non-`sigil` attribute is out-of-subset (fail-closed).
    assert_eq!(
        first_code("#[inline]\npub fn f(n: i64) -> i64 { return n; }"),
        codes::FE010_UNKNOWN_ANNOTATION
    );
    // FE010: a malformed `sigil::cap` attribute (missing the deadline).
    assert_eq!(
        first_code("#[sigil::cap(Net)]\npub fn f(n: i64) -> i64 { return n; }"),
        codes::FE010_UNKNOWN_ANNOTATION
    );
    // FE620: a capability type name colliding with a function name.
    assert_eq!(
        first_code("#[sigil::cap(f, deadline = 1)]\npub fn f(n: i64) -> i64 { return n; }"),
        codes::FE620_BAD_IDENTIFIER_RS
    );
    // FE612: a deadline out of i64 range.
    assert_eq!(
        first_code(
            "#[sigil::cap(Net, deadline = 99999999999999999999)]\npub fn f(n: i64) -> i64 { return n; }"
        ),
        codes::FE612_BAD_NUMBER_RS
    );

    // ── RS2: effects ──
    // FE213: a compiler-reserved effect name (Unsafe / FFI / Alloc).
    assert_eq!(
        first_code("#[sigil::effects(Unsafe)]\npub fn f(n: i64) -> i64 { return n; }"),
        codes::FE213_RESERVED_EFFECT
    );
    // An empty `#[sigil::effects()]` still selects effect-mode (outer ring).
    let empty = translate_ok(
        "#[sigil::effects()]\npub fn f(n: i64) -> i64 { return n; }",
        "m.rs",
    );
    assert!(
        empty.text.contains("#[ring(outer)]"),
        "empty effects must select effect-mode; got:\n{}",
        empty.text
    );
    assert!(
        empty.text.contains("! { }"),
        "a fn with empty effects must emit an empty row; got:\n{}",
        empty.text
    );
    // Effects emit lexicographically sorted + byte-stable.
    let sorted = translate_ok(
        "#[sigil::effects(NetIO, Crypto, FsIO)]\npub fn f(n: i64) -> i64 { return n; }",
        "m.rs",
    );
    assert!(
        sorted.text.contains("! { Crypto, FsIO, NetIO }"),
        "effect row must be lexicographically sorted; got:\n{}",
        sorted.text
    );

    // ── RS3: structs (records) ──
    // FE640: constructing with a field the struct does not declare.
    assert_eq!(
        first_code("struct P { x: i64 }\npub fn f(n: i64) -> P { return P { x: n, y: n }; }"),
        codes::FE640_STRUCT_FIELD_MISMATCH_RS
    );
    // FE640: the same field supplied twice in one construction.
    assert_eq!(
        first_code(
            "struct P { x: i64, y: i64 }\npub fn f(n: i64) -> P { return P { x: n, x: n, y: n }; }"
        ),
        codes::FE640_STRUCT_FIELD_MISMATCH_RS
    );
    // FE640: a duplicate field in the struct *declaration*.
    assert_eq!(
        first_code("struct P { x: i64, x: bool }\npub fn f() -> i64 { return 0; }"),
        codes::FE640_STRUCT_FIELD_MISMATCH_RS
    );
    // FE642: field access on a scalar (non-struct) value.
    assert_eq!(
        first_code("pub fn f(a: i64) -> i64 { return a.x; }"),
        codes::FE642_BAD_FIELD_ACCESS_RS
    );
    // FE642: constructing a struct that was never declared.
    assert_eq!(
        first_code("pub fn f() -> i64 { return Ghost { x: 1 }; }"),
        codes::FE642_BAD_FIELD_ACCESS_RS
    );
    // FE620: a struct name colliding with a function name (would be N002, invisible
    // to the FE500 parse self-check).
    assert_eq!(
        first_code("struct f { x: i64 }\npub fn f() -> i64 { return 0; }"),
        codes::FE620_BAD_IDENTIFIER_RS
    );
    // FE641: a generic struct is out-of-subset.
    assert_eq!(
        first_code("struct P<T> { x: T }\npub fn f() -> i64 { return 0; }"),
        codes::FE641_BAD_STRUCT_SHAPE_RS
    );
    // FE641: a directly self-referential struct (infinite size).
    assert_eq!(
        first_code("struct N { next: N }\npub fn f() -> i64 { return 0; }"),
        codes::FE641_BAD_STRUCT_SHAPE_RS
    );
    // FE610: a struct field of an unknown type.
    assert_eq!(
        first_code("struct P { x: Widget }\npub fn f() -> i64 { return 0; }"),
        codes::FE610_UNSUPPORTED_TYPE_RS
    );
    // FE630: `==`/`!=` on struct values is unsupported (scalars only).
    assert_eq!(
        first_code("struct P { x: i64 }\npub fn f(p: P, q: P) -> bool { return p == q; }"),
        codes::FE630_ILL_TYPED_RS
    );

    // ── RS3b: enums + `match` ──
    // FE650: unsupported enum shapes — generic, empty, duplicate variant.
    assert_eq!(
        first_code("enum E<T> { A }\npub fn f() -> i64 { return 0; }"),
        codes::FE650_BAD_ENUM_SHAPE_RS
    );
    assert_eq!(
        first_code("enum E {}\npub fn f() -> i64 { return 0; }"),
        codes::FE650_BAD_ENUM_SHAPE_RS
    );
    assert_eq!(
        first_code("enum E { A, A }\npub fn f() -> i64 { return 0; }"),
        codes::FE650_BAD_ENUM_SHAPE_RS
    );
    // FE652: an undeclared enum in construction.
    assert_eq!(
        first_code("pub fn f() -> i64 { let x = Ghost::X; return 0; }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE652: constructing a dataless variant with a payload (arity 0 ≠ 1).
    assert_eq!(
        first_code("enum E { A }\npub fn f() -> i64 { return E::A(5); }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE652: a variant pattern against a non-enum scrutinee.
    assert_eq!(
        first_code("pub fn f(n: i64) -> i64 { match n { E::A => 1, _ => 0 } }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE652: a literal pattern whose type ≠ the (enum) scrutinee.
    assert_eq!(
        first_code("enum Color { Red }\npub fn f(c: Color) -> i64 { match c { 0 => 1, _ => 0 } }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE652: a duplicate literal arm.
    assert_eq!(
        first_code("pub fn f(n: i64) -> i64 { match n { 0 => 1, 0 => 2, _ => 3 } }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE652: an arm after a `_` catch-all is unreachable.
    assert_eq!(
        first_code("pub fn f(n: i64) -> i64 { match n { _ => 1, 0 => 2 } }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE651: a non-exhaustive `bool` match (missing `false`, no `_`).
    assert_eq!(
        first_code("pub fn f(b: bool) -> i64 { match b { true => 1 } }"),
        codes::FE651_NONEXHAUSTIVE_MATCH_RS
    );
    // FE620: an enum name colliding with a function name.
    assert_eq!(
        first_code("enum f { A }\npub fn f() -> i64 { return 0; }"),
        codes::FE620_BAD_IDENTIFIER_RS
    );
    // FE620: a variant name colliding with a SIGIL keyword (emit-safety, SC-2).
    assert_eq!(
        first_code("enum E { state }\npub fn f() -> i64 { return 0; }"),
        codes::FE620_BAD_IDENTIFIER_RS
    );
    // FE690: `match` in value/expression position is deferred (statement only).
    assert_eq!(
        first_code("pub fn f(n: i64) -> i64 { let x = match n { _ => 1 }; return x; }"),
        codes::FE690_EXPR_POSITION_RS
    );
    // FE630: a match arm value whose type ≠ the function return type.
    assert_eq!(
        first_code("pub fn f(n: i64) -> bool { match n { 0 => 1, _ => false } }"),
        codes::FE630_ILL_TYPED_RS
    );

    // ── RS3c: enum payloads + pattern bindings ──
    // FE652: construction arity mismatch (a 1-field variant given 2 args).
    assert_eq!(
        first_code("enum E { A(i64) }\npub fn f() -> E { return E::A(1, 2); }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE652: pattern-binding arity mismatch (a 1-field variant bound with 2).
    assert_eq!(
        first_code("enum E { A(i64) }\npub fn f(e: E) -> i64 { match e { E::A(x, y) => x } }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE652: a `_` payload placeholder is deferred (name the binding).
    assert_eq!(
        first_code("enum E { A(i64, i64) }\npub fn f(e: E) -> i64 { match e { E::A(_, y) => y } }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE652: the same payload binding twice in one pattern.
    assert_eq!(
        first_code("enum E { A(i64, i64) }\npub fn f(e: E) -> i64 { match e { E::A(x, x) => x } }"),
        codes::FE652_BAD_MATCH_ARM_RS
    );
    // FE630: a payload argument whose type ≠ the variant's field.
    assert_eq!(
        first_code("enum E { A(i64) }\npub fn f() -> E { return E::A(true); }"),
        codes::FE630_ILL_TYPED_RS
    );
    // FE610: a variant payload of an unknown type.
    assert_eq!(
        first_code("enum E { A(Widget) }\npub fn f() -> i64 { return 0; }"),
        codes::FE610_UNSUPPORTED_TYPE_RS
    );
    // FE635: a payload binding shadowing a binding already in scope.
    assert_eq!(
        first_code("enum E { A(i64) }\npub fn f(e: E, v: i64) -> i64 { match e { E::A(v) => v } }"),
        codes::FE635_SHADOWING_RS
    );
    // FE620: a payload binding whose name collides with a SIGIL keyword (SC-2).
    assert_eq!(
        first_code("enum E { A(i64) }\npub fn f(e: E) -> i64 { match e { E::A(state) => 0 } }"),
        codes::FE620_BAD_IDENTIFIER_RS
    );

    // ── RS4a: `#[sigil::requires]` refinement preconditions ──
    // FE660: a non-identifier LHS (a vacuous `1 == 1` — SR-2).
    assert_eq!(
        first_code("#[sigil::requires(1 == 1)]\npub fn f(x: i64) -> i64 { x }"),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // FE660: `=` is not a comparison operator (`==` is).
    assert_eq!(
        first_code("#[sigil::requires(x = 0)]\npub fn f(x: i64) -> i64 { x }"),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // FE660: a parameter right-hand side (`x < y`) is deferred to RS4b (AG-1).
    assert_eq!(
        first_code("#[sigil::requires(x < y)]\npub fn f(x: i64, y: i64) -> i64 { x }"),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // FE660: a negative bound is deferred (non-negative literal RHS in RS4a).
    assert_eq!(
        first_code("#[sigil::requires(x >= -5)]\npub fn f(x: i64) -> i64 { x }"),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // FE660: two `#[sigil::requires]` on one function (AG-2).
    assert_eq!(
        first_code(
            "#[sigil::requires(x > 0)]\n#[sigil::requires(x < 9)]\npub fn f(x: i64) -> i64 { x }"
        ),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // FE660: `#[sigil::requires]` mixed with a capability (AG-4, deferred).
    assert_eq!(
        first_code(
            "#[sigil::requires(x > 0)]\n#[sigil::cap(Net, deadline = 9)]\npub fn f(x: i64) -> i64 { x }"
        ),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // FE661: the predicate references a name that is not a parameter (SR-3).
    assert_eq!(
        first_code("#[sigil::requires(y > 0)]\npub fn f(x: i64) -> i64 { x }"),
        codes::FE661_REFINEMENT_UNKNOWN_PARAM_RS
    );
    // Every comparison operator is accepted + emitted 1:1 (fragment shape, SR-1).
    for (src_op, sig_op) in [
        ("<", "<"),
        ("<=", "<="),
        (">", ">"),
        (">=", ">="),
        ("==", "=="),
        ("!=", "!="),
    ] {
        let src = format!("#[sigil::requires(x {src_op} 3)]\npub fn f(x: i64) -> i64 {{ x }}");
        let emitted = translate_ok(&src, "op.rs");
        assert!(
            emitted.text.contains(&format!("where x {sig_op} 3")),
            "operator `{src_op}` must emit `where x {sig_op} 3`; got:\n{}",
            emitted.text
        );
    }

    // ── RS4b: `#[sigil::invariant]` record refinements ──
    // FE660: an invariant on a function (it is struct-only).
    assert_eq!(
        first_code("#[sigil::invariant(x > 0)]\npub fn f(x: i64) -> i64 { x }"),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // FE661: the invariant references a name that is not a field.
    assert_eq!(
        first_code(
            "#[sigil::invariant(missing >= 0)]\nstruct S { x: i64 }\npub fn f(s: S) -> i64 { s.x }"
        ),
        codes::FE661_REFINEMENT_UNKNOWN_PARAM_RS
    );
    // FE660: a non-i64 invariant field.
    assert_eq!(
        first_code(
            "#[sigil::invariant(b >= 0)]\nstruct S { b: bool, n: i64 }\npub fn f(s: S) -> i64 { s.n }"
        ),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // FE660: a self-referential (vacuous) cross-field clause.
    assert_eq!(
        first_code(
            "#[sigil::invariant(x == x)]\nstruct S { x: i64 }\npub fn f(s: S) -> i64 { s.x }"
        ),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // FE661: a cross-field RHS that is not a field.
    assert_eq!(
        first_code(
            "#[sigil::invariant(lo <= ghost)]\nstruct S { lo: i64 }\npub fn f(s: S) -> i64 { s.lo }"
        ),
        codes::FE661_REFINEMENT_UNKNOWN_PARAM_RS
    );
    // FE660: two invariants on one struct (single clause in RS4b).
    assert_eq!(
        first_code(
            "#[sigil::invariant(x > 0)]\n#[sigil::invariant(x < 9)]\nstruct S { x: i64 }\npub fn f(s: S) -> i64 { s.x }"
        ),
        codes::FE660_BAD_REFINEMENT_RS
    );
    // A cross-field invariant emits a record `where` clause naming both fields.
    let xf = translate_ok(
        "#[sigil::invariant(lo <= hi)]\nstruct R { lo: i64, hi: i64 }\npub fn f(r: R) -> i64 { r.lo }",
        "xf.rs",
    );
    assert!(
        xf.text
            .contains("record R { lo: i64, hi: i64 } where lo <= hi"),
        "cross-field invariant must emit `where lo <= hi`; got:\n{}",
        xf.text
    );

    // ── RS5a: `#[sigil::taint]` information-flow labels ──
    // FE670: an unknown taint level.
    assert_eq!(
        first_code("#[sigil::taint(s = Confidential)]\npub fn f(s: i64) -> i64 { s }"),
        codes::FE670_BAD_TAINT_RS
    );
    // FE670: `SecretCT` (constant-time) is deferred.
    assert_eq!(
        first_code("#[sigil::taint(s = SecretCT)]\npub fn f(s: i64) -> i64 { s }"),
        codes::FE670_BAD_TAINT_RS
    );
    // FE670: an empty attribute.
    assert_eq!(
        first_code("#[sigil::taint()]\npub fn f(s: i64) -> i64 { s }"),
        codes::FE670_BAD_TAINT_RS
    );
    // FE670: a duplicate target (never last-wins, SR-T3).
    assert_eq!(
        first_code("#[sigil::taint(s = Secret, s = Public)]\npub fn f(s: i64) -> i64 { s }"),
        codes::FE670_BAD_TAINT_RS
    );
    // FE670: a taint target on a non-scalar (struct) type (SR-T10).
    assert_eq!(
        first_code(
            "struct P { x: i64 }\n#[sigil::taint(p = Secret)]\npub fn f(p: P) -> i64 { p.x }"
        ),
        codes::FE670_BAD_TAINT_RS
    );
    // FE670: `#[sigil::taint]` on an enum (function-only).
    assert_eq!(
        first_code("#[sigil::taint(x = Secret)]\nenum E { A }\npub fn f() -> i64 { return 0; }"),
        codes::FE670_BAD_TAINT_RS
    );
    // FE670: taint mixed with a refinement (AG-T7 mode gate).
    assert_eq!(
        first_code(
            "#[sigil::taint(s = Secret)]\n#[sigil::requires(s > 0)]\npub fn f(s: i64) -> i64 { s }"
        ),
        codes::FE670_BAD_TAINT_RS
    );
    // FE671: a target that is neither `ret` nor a parameter.
    assert_eq!(
        first_code("#[sigil::taint(x = Secret)]\npub fn f(s: i64) -> i64 { s }"),
        codes::FE671_TAINT_UNKNOWN_TARGET_RS
    );
    // Each level emits the exact case-sensitive `@Label` (SR-T8), on param + return.
    for (src_lvl, sig_lvl) in [
        ("Public", "Public"),
        ("Internal", "Internal"),
        ("Secret", "Secret"),
    ] {
        let src = format!(
            "#[sigil::taint(s = {src_lvl}, ret = {src_lvl})]\npub fn f(s: i64) -> i64 {{ s }}"
        );
        let emitted = translate_ok(&src, "t.rs");
        assert!(
            emitted.text.contains(&format!("s: i64 @{sig_lvl}"))
                && emitted.text.contains(&format!("-> i64 @{sig_lvl}")),
            "level `{src_lvl}` must emit `@{sig_lvl}` on param + return; got:\n{}",
            emitted.text
        );
    }

    // ── RS5b: `declassify` conformance ──────────────────────────────────────────
    // FE672: wrong arity (SR-B1).
    assert_eq!(
        first_code("pub fn f(s: i64) -> i64 { declassify() }"),
        codes::FE672_BAD_DECLASSIFY_RS
    );
    assert_eq!(
        first_code("pub fn f(a: i64, b: i64) -> i64 { declassify(a, b) }"),
        codes::FE672_BAD_DECLASSIFY_RS
    );
    // FE672: a non-scalar (struct-typed) declassify argument (SR-B2 / AG-B3).
    assert_eq!(
        first_code("struct P { x: i64 }\npub fn f(p: P) -> i64 { let q = declassify(p); 0 }"),
        codes::FE672_BAD_DECLASSIFY_RS
    );
    // FE672: `declassify_ct` is deferred to RS5c (AG-B1 / SR-B3).
    assert_eq!(
        first_code("pub fn f(s: i64) -> i64 { declassify_ct(s) }"),
        codes::FE672_BAD_DECLASSIFY_RS
    );
    // FE672: declassify mixed with a cap (SR-B6 mode gate).
    assert_eq!(
        first_code(
            "#[sigil::cap(NetIO, deadline = 2030)]\npub fn f(s: i64) -> i64 { declassify(s) }"
        ),
        codes::FE672_BAD_DECLASSIFY_RS
    );
    // FE040: a declassify-bearing fn is a leaf — an intra-program call is rejected
    // pre-emit (SR-B5), reusing the RS1 cap-callee gate.
    assert_eq!(
        first_code(
            "#[sigil::taint(s = Secret)]\nfn reveal(s: i64) -> i64 { declassify(s) }\npub fn c(s: i64) -> i64 { reveal(s) }"
        ),
        codes::FE040_CAP_CALLEE
    );
    // Emit shape: `declassify(s)` lowers to the SIGIL keyword form with a synthesized
    // linear cap, and the empty `Declassify` cap type is co-emitted once.
    let dc = translate_ok(
        "#[sigil::taint(s = Secret)]\npub fn r(s: i64) -> i64 { declassify(s) }",
        "t.rs",
    );
    assert!(
        dc.text.contains("cap type Declassify {}")
            && dc.text.contains("declassify(s, __fe_declassify_cap_0)")
            && dc.text.contains("__fe_declassify_cap_0: Declassify"),
        "declassify must lower to `declassify(v, cap)` with a synthesized cap; got:\n{}",
        dc.text
    );
}

// ── SC-7: oracle agreement — every ACCEPTED input compiles with ZERO compiler
// errors, so the translator's sound checker (not the oracle) is what rejects
// ill-typed programs. If the checker were unsound (e.g. uniform-i64), one of
// these would emit a T-code. ──────────────────────────────────────────────────
#[test]
fn accepted_inputs_emit_zero_tcode_sigil() {
    let snippets = [
        "pub fn a(x: i64, y: i64) -> i64 { x + y * 2 - 1 }",
        "pub fn a(x: i64, y: i64) -> bool { x < y }",
        "pub fn a(x: i64, y: i64) -> bool { x <= y }",
        "pub fn a(x: i64, y: i64) -> bool { x > y }",
        "pub fn a(x: i64, y: i64) -> bool { x >= y }",
        "pub fn a(x: i64, y: i64) -> bool { x == y }",
        "pub fn a(x: i64, y: i64) -> bool { x != y }",
        "pub fn a(x: bool, y: bool) -> bool { x == y }",
        "pub fn a(x: i64) -> i64 { -x }",
        "pub fn a(x: bool) -> bool { !x }",
        "pub fn a(x: i64) -> i64 { return x * (x + 1); }",
        // A non-`pub` top-level fn + a cross-call (visibility is preserved).
        "fn id(x: i64) -> i64 { x }\npub fn a(x: i64) -> i64 { id(x) }",
        // Increment 2: locals, if/else, while, and return-path variants.
        "pub fn a(x: i64) -> i64 { let mut r: i64 = x; if x < 0 { r = 0; } else {} return r; }",
        "pub fn a(n: i64) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < n { s = s + i; i = i + 1; } return s; }",
        // A body that returns via an if/else with both branches returning (no
        // trailing return) — exercises SIGIL's own exhaustiveness (T044).
        "pub fn a(x: i64) -> i64 { if x > 0 { return 1; } else { return 2; } }",
        // A `bool` local + a bare-`bool` condition (no parens around the cond).
        "pub fn a(x: i64, y: i64) -> bool { let c: bool = x < y; return c; }",
        "pub fn a(b: bool) -> i64 { if b { return 1; } else { return 0; } }",
        "pub fn a(x: i64) -> i64 { let mut v: i64 = x; v = v + 1; return v; }",
        // RS1: a cap-bearing fn compiles clean with no build-deadline.
        "#[sigil::cap(Fs, deadline = 3000)]\npub fn a(n: i64) -> i64 { return n * 2; }",
        // RS2: effect-mode; `hi` declares NetIO and calls `lo` (NetIO) → no leak.
        "#[sigil::effects(NetIO)]\npub fn lo(n: i64) -> i64 { return n; }\n#[sigil::effects(NetIO)]\npub fn hi(n: i64) -> i64 { return lo(n); }",
        // RS3: a record — construct (out of decl order) + field access.
        "struct P { x: i64, y: i64 }\npub fn area(p: P) -> i64 { return p.x * p.y; }\npub fn mk(a: i64) -> P { return P { y: a, x: a }; }",
        // RS3: a bool struct field read in an `if` condition (field access is not a
        // struct literal, so the no-struct-literal-in-condition rule does not fire).
        "struct Flag { active: bool, n: i64 }\npub fn pick(fl: Flag) -> i64 { if fl.active { return fl.n; } else { return 0; } }",
        // RS3: a nested record — record-typed field, nested construct + `a.b.c`.
        "struct Inner { v: i64 }\nstruct Outer { inner: Inner, tag: bool }\npub fn get(o: Outer) -> i64 { return o.inner.v; }\npub fn wrap(n: i64) -> Outer { return Outer { inner: Inner { v: n }, tag: true }; }",
        // RS3b: an enum exhaustively matched by variant coverage (no `_`).
        "enum E { A, B }\npub fn f(e: E) -> i64 { match e { E::A => 1, E::B => 2 } }",
        // RS3b: an enum match with a `_` catch-all; and enum construction.
        "enum Sig { Go, Stop, Wait }\npub fn ok(s: Sig) -> bool { match s { Sig::Go => true, _ => false } }\npub fn start() -> Sig { Sig::Go }",
        // RS3b: an `i64` match (wildcard-exhaustive) and a `bool` match (both values).
        "pub fn f(n: i64) -> i64 { match n { 0 => 1, _ => n } }\npub fn g(b: bool) -> i64 { match b { true => 1, false => 0 } }",
        // RS3b × RS3a: an enum-typed struct field, constructed into a fresh record.
        // (Returning `p.c` from a `@ReadOnly` param would alias — T253 — so this
        // row constructs + returns a fresh `Pixel` and reads only the scalar field.)
        "enum Color { Red, Green }\nstruct Pixel { c: Color, n: i64 }\npub fn size(p: Pixel) -> i64 { return p.n; }\npub fn mk(n: i64) -> Pixel { return Pixel { c: Color::Red, n: n }; }",
        // RS3c: a payload variant — construct with an arg, bind + read it in a match.
        "enum Opt { Some(i64), None }\npub fn unwrap(o: Opt, d: i64) -> i64 { match o { Opt::Some(v) => v, Opt::None => d } }\npub fn mk(n: i64) -> Opt { Opt::Some(n) }",
        // RS3c: a `bool` payload bound + returned; and a dataless variant alongside.
        "enum Flag { On(bool), Off }\npub fn f(fl: Flag) -> bool { match fl { Flag::On(b) => b, Flag::Off => false } }",
        // RS3c: a multi-field payload variant, both fields bound + used.
        "enum Pair { P(i64, i64) }\npub fn sum(p: Pair) -> i64 { match p { Pair::P(a, b) => a + b } }",
        // RS3c: a payload variant that is declared but unused (was the RS3b FE650
        // reject `payload_variant.rs`; now accepted).
        "enum MyOption { Some(i64), None }\npub fn f() -> i64 { return 0; }",
        // RS5a: taint labels (each row emits ≥1 `@Level` and compiles clean — SR-T6).
        // Upward flow `Secret -> Secret`.
        "#[sigil::taint(s = Secret, ret = Secret)]\npub fn f(s: i64) -> i64 { s }",
        // Multi-param lub (`Secret` lub `Internal` = `Secret`) into a `Secret` return.
        "#[sigil::taint(a = Secret, b = Internal, ret = Secret)]\npub fn f(a: i64, b: i64) -> i64 { a + b }",
        // A tainted param the body never flows to a `Public` return (pins AG-T3).
        "#[sigil::taint(a = Internal)]\npub fn f(a: i64) -> i64 { 0 }",
        // RS5b: the `declassify` escape hatch (each row does a real @Secret->@Public
        // downgrade authorized by a synthesized linear cap — SR-B8).
        "#[sigil::taint(s = Secret)]\npub fn reveal(s: i64) -> i64 { declassify(s) }",
        // Two independent declassifies → two distinct caps, both consumed (AG-B2).
        "#[sigil::taint(a = Secret, b = Secret)]\npub fn two(a: i64, b: i64) -> i64 { let x = declassify(a); declassify(b) }",
        // A declassify nested inside an arithmetic expression (SR-B10).
        "#[sigil::taint(a = Secret)]\npub fn bump(a: i64) -> i64 { declassify(a) + 1 }",
    ];
    for s in snippets {
        let emitted = translate_ok(s, "g.rs");
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

// ── Determinism: identical input → byte-identical output ─────────────────────
#[test]
fn deterministic_emission() {
    let src = "pub fn f(a: i64, b: i64) -> i64 { return a + b * 2; }";
    let a = translate_ok(src, "x.rs").text;
    let b = translate_ok(src, "x.rs").text;
    assert_eq!(a, b);
}

// ── SC-8: depth cap — deep nesting fails fast with FE602, no stack overflow ───
#[test]
fn depth_cap_rejects_without_overflow() {
    let mut e = String::from("a");
    for _ in 0..200 {
        e = format!("({e})");
    }
    let src = format!("pub fn f(a: i64) -> i64 {{ {e} }}");
    assert_eq!(first_code(&src), codes::FE602_TOO_LARGE_RS);
}

// The depth guard lives in parse_unary, so it must also bound recursion that
// re-enters via the call-argument path, not just parentheses.
#[test]
fn depth_cap_covers_nested_calls() {
    let mut e = String::from("a");
    for _ in 0..200 {
        e = format!("f({e})");
    }
    let src = format!("pub fn f(a: i64) -> i64 {{ {e} }}");
    assert_eq!(first_code(&src), codes::FE602_TOO_LARGE_RS);
}

// Block nesting (if-statements) shares the same depth counter, so deeply nested
// blocks also fail fast with FE602 rather than overflowing the native stack.
#[test]
fn block_depth_cap_rejects_without_overflow() {
    let mut body = String::from("return 0;");
    for _ in 0..200 {
        body = format!("if true {{ {body} }} else {{ return 0; }}");
    }
    let src = format!("pub fn f() -> i64 {{ {body} }}");
    assert_eq!(first_code(&src), codes::FE602_TOO_LARGE_RS);
}

// ── Totality: never panics / hangs on arbitrary input ───────────────────────
proptest! {
    #[test]
    fn never_panics_on_arbitrary_input(s in ".{0,400}") {
        let _ = rs().translate(&s, "fuzz.rs");
    }

    #[test]
    fn never_panics_on_tokenish_input(
        s in proptest::collection::vec(
            prop::sample::select(vec![
                "pub", "fn", " ", "(", ")", "{", "}", ":", ";", ",", "i64", "bool",
                "return", "+", "-", "*", "<", "<=", ">", "==", "!=", "!", "->",
                "true", "false", "let", "if", "a", "1", "/", "&", "\n",
            ]),
            0..40,
        ).prop_map(|v| v.join(" "))
    ) {
        let _ = rs().translate(&s, "fuzz.rs");
    }

    // SR-4: the `#[sigil::requires]` predicate mini-parser is total — arbitrary
    // attribute bodies never panic or hang, only translate-or-reject.
    #[test]
    fn never_panics_on_arbitrary_requires_attr(body in ".{0,80}") {
        let src = format!("#[sigil::requires({body})]\npub fn f(x: i64) -> i64 {{ x }}");
        let _ = rs().translate(&src, "fuzz.rs");
    }

    // SR-T4: the `#[sigil::taint]` target-list mini-parser is total.
    #[test]
    fn never_panics_on_arbitrary_taint_attr(body in ".{0,80}") {
        let src = format!("#[sigil::taint({body})]\npub fn f(s: i64) -> i64 {{ s }}");
        let _ = rs().translate(&src, "fuzz.rs");
    }

    // SR-B10: the `declassify(...)` recognition + arity check is total — an arbitrary
    // call body never panics or hangs, only translate-or-reject.
    #[test]
    fn never_panics_on_arbitrary_declassify(body in ".{0,80}") {
        let src = format!("#[sigil::taint(s = Secret)]\npub fn f(s: i64) -> i64 {{ declassify({body}) }}");
        let _ = rs().translate(&src, "fuzz.rs");
    }
}
