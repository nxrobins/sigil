//! SH-MONO — the monomorphizer differential (`selfhost/monomorph.sigil` vs the oracle's
//! inline-in-typecheck instantiation).
//!
//! THE ORACLE OBSERVABLE: monomorphization is INLINE in type-checking — instances are created
//! on-demand at call sites (`infer_call_expr` expressions.rs:1704-1956, `infer_method_call_expr`
//! :5518-5714), cache-dedup'd in a `MonomorphTracker`, and drained into
//! `TypedProgram.modules[0].functions` (type_check/mod.rs:808-812) as structurally ordinary
//! functions whose mangled NAME (`name__T1$T2`, air.rs `mangle_type`) is their identity. The
//! generic SOURCE fn is DROPPED at collection (mod.rs:377 admits only `type_params.is_empty()`).
//! So the differential target is the ORDERED function list of the typed program (+ the concrete
//! record/enum layout keys) — no new compiler hook needed.
//!
//! THE MONO-0 PHASE-0 PINS (each an empirical answer the shadow design depends on):
//! - the generic source is ABSENT; instances append AFTER the module's monomorphic fns;
//! - instance order is CALL-ENCOUNTER order for independent calls, but POST-ORDER (completion
//!   order) for transitive instantiation — `outer(5)` whose body calls `inner(x)` lists
//!   `inner__i64` BEFORE `outer__i64` (the callee's TypedFunction is pushed when its body-check
//!   completes, inside the caller's own instantiation);
//! - args-before-call: `id(wrap(5))` registers `wrap__i64` before `id__i64`;
//! - ALL instances drain into the FIRST module (`modules.first_mut()`), even a later module's;
//! - the binding rule is FIRST-TOP-LEVEL-BINDING-WINS (resolve.rs:886-903): `id2(5, x: u32)`
//!   → `id2__i64` (the literal binds T weakly but top-level concretes do NOT override);
//!   `id2(x, 5)` → `id2__u32` — the X-M7 discriminator pair;
//! - dedup is by mangled name; self-recursion registers ONCE (cache-before-check);
//! - mangle: `pair__i64$str` ($-join), nested `use_it__BoxG__i64`, impl method
//!   `BoxG__get__i64` ({Type}__{method}__{targs});
//! - LAYOUT ASYMMETRY: a constructed generic ENUM registers a concrete layout key
//!   (`OptG__i64`) but a constructed generic RECORD does NOT (records keep only `BoxG`);
//! - corpus discipline: a generic body may NOT annotate a let with a bare type-param
//!   (`let y: T = …` → T046) — transitive fixtures use unannotated lets; returning a
//!   record-typed param trips T253 — record type-args ride non-returning generics.
//!
//! Census slices (MONO-1/2) compare SORTED name lists; the byte slices (MONO-3+) compare the
//! ORDER too (fn order = FuncId basis = wasm byte identity, X-M8).

use sigil_compiler::CompileOptions;
use sigil_compiler::name_resolution;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use sigil_compiler::type_check;
use sigil_compiler::typed_ast::TypedFunctionKind;

const EXECUTION_FUEL: u64 = 300_000_000;

/// The bare tail after the last `::` (the module-qualification strip, the air-lane convention).
fn bare_tail(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// The oracle's ORDERED function census: parse → resolve → type-check, then every module's
/// functions in program order as `bare_tail(kind)` entries — instances included, generic
/// sources dropped (by the oracle itself). Returns Err(codes) on a resolve/type-check
/// rejection so reject-path pins stay loud.
fn oracle_functions(label: &str, src: &str) -> Result<Vec<String>, Vec<String>> {
    let source = SourceFile::new("<mono-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(
        pdiags.is_empty(),
        "SH-MONO {label}: fixture must be parse-clean, got {:?}\n{src}",
        pdiags
            .iter()
            .map(|d| d.code().to_string())
            .collect::<Vec<_>>()
    );
    let resolved = match name_resolution::resolve(&ast) {
        Ok(r) => r,
        Err(ds) => {
            return Err(ds.iter().map(|d| d.code().to_string()).collect());
        }
    };
    let (typed, _) = match type_check::check_with_options(&resolved, &CompileOptions::default()) {
        Ok(pair) => pair,
        Err(ds) => {
            return Err(ds.iter().map(|d| d.code().to_string()).collect());
        }
    };
    let mut out = Vec::new();
    for module in &typed.modules {
        for f in &module.functions {
            let kind = match &f.kind {
                TypedFunctionKind::ModuleInit => "MI",
                TypedFunctionKind::ModuleFunction => "F",
                TypedFunctionKind::ActorInit { .. } => "AI",
                TypedFunctionKind::ActorHandler { .. } => "AH",
                TypedFunctionKind::Closure => "C",
            };
            out.push(format!("{}({kind})", bare_tail(&f.name)));
        }
    }
    Ok(out)
}

/// The concrete record/enum layout keys (the tracker drain's second observable —
/// `TypedProgram.records`/`.enums` are BTreeMaps, so keys come out sorted).
fn oracle_layout_keys(label: &str, src: &str) -> (Vec<String>, Vec<String>) {
    let source = SourceFile::new("<mono-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(pdiags.is_empty(), "SH-MONO {label}: parse-clean");
    let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
    let (typed, _) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .expect("fixture must type-check");
    (
        typed.records.keys().cloned().collect(),
        typed.enums.keys().cloned().collect(),
    )
}

/// The Phase-0 census pins: (label, fixture, the expected ORDERED `bare(kind)` list). Every
/// entry is an empirically-pinned oracle answer the MONO-1+ shadow must reproduce.
const MONO_CENSUS_PINS: &[(&str, &str, &[&str])] = &[
    // The minimal instance set: generic source dropped, instances in call order.
    (
        "p_min",
        "module m;\nfn id<T>(x: T) -> T { return x; }\nfn test() -> i64 { let a: i64 = id(5); let b: bool = id(true); return a; }\n",
        &["test(F)", "id__i64(F)", "id__bool(F)"],
    ),
    // Dedup: two i64 calls, one instance (cache-before-check, expressions.rs:1864).
    (
        "p_dedup",
        "module m;\nfn id<T>(x: T) -> T { return x; }\nfn test() -> i64 { let a: i64 = id(5); let b: i64 = id(6); return a + b; }\n",
        &["test(F)", "id__i64(F)"],
    ),
    // An uncalled generic produces NOTHING.
    (
        "p_uncalled",
        "module m;\nfn id<T>(x: T) -> T { return x; }\nfn test() -> i64 { return 7; }\n",
        &["test(F)"],
    ),
    // Args-before-call: the inner call's instance registers first.
    (
        "p_nested",
        "module m;\nfn wrap<T>(x: T) -> T { return x; }\nfn id<T>(x: T) -> T { return x; }\nfn test() -> i64 { let a: i64 = id(wrap(5)); return a; }\n",
        &["test(F)", "wrap__i64(F)", "id__i64(F)"],
    ),
    // Transitive is POST-ORDER: outer's body-check registers inner and PUSHES inner's
    // TypedFunction before outer's own push completes. (Generic bodies may not annotate
    // lets with a bare type-param — T046 — hence the unannotated `let y`.)
    (
        "p_transitive",
        "module m;\nfn inner<T>(x: T) -> T { return x; }\nfn outer<T>(x: T) -> T { let y = inner(x); return y; }\nfn test() -> i64 { let a: i64 = outer(5); return a; }\n",
        &["test(F)", "inner__i64(F)", "outer__i64(F)"],
    ),
    // Independent calls: call-encounter order (gb called before ga), not decl order.
    (
        "p_two_generics_order",
        "module m;\nfn ga<T>(x: T) -> T { return x; }\nfn gb<T>(x: T) -> T { return x; }\nfn test() -> i64 { let s: str = \"x\"; let b: str = gb(s); let a: i64 = ga(1); return a; }\n",
        &["test(F)", "gb__str(F)", "ga__i64(F)"],
    ),
    // ALL instances drain into the FIRST module (mod.rs:810 modules.first_mut()) — module b's
    // idb__i64 lands between module a's fns and module b's tb.
    (
        "p_twomod",
        "module a;\nfn ida<T>(x: T) -> T { return x; }\nfn ta() -> i64 { let r: i64 = ida(1); return r; }\nmodule b;\nfn idb<T>(x: T) -> T { return x; }\nfn tb() -> i64 { let r: i64 = idb(2); return r; }\n",
        &["ta(F)", "ida__i64(F)", "idb__i64(F)", "tb(F)"],
    ),
    // THE X-M7 DISCRIMINATOR PAIR — first-top-level-binding-wins (resolve.rs:886-903):
    // the literal binds T first → id2__i64 (u32 does NOT override at top level)…
    (
        "p_mixed_annotated",
        "module m;\nfn id2<T>(a: T, b: T) -> T { return a; }\nfn test(x: u32) -> u32 { let r: u32 = id2(5, x); return r; }\n",
        &["test(F)", "id2__i64(F)"],
    ),
    // …and the concrete-first order binds u32.
    (
        "p_mixed_concrete_first",
        "module m;\nfn id2<T>(a: T, b: T) -> T { return a; }\nfn test(x: u32) -> u32 { let r: u32 = id2(x, 5); return r; }\n",
        &["test(F)", "id2__u32(F)"],
    ),
    // Multi-type-param mangle: $-join.
    (
        "p_pair",
        "module m;\nfn pair<A, B>(a: A, b: B) -> A { return a; }\nfn test() -> i64 { let s: str = \"x\"; let r: i64 = pair(7, s); return r; }\n",
        &["test(F)", "pair__i64$str(F)"],
    ),
    // A record type-arg (via a NON-returning generic — returning a record param is T253).
    (
        "p_record_targ",
        "module m;\nrecord P { x: i64 }\nfn use_it<T>(x: T) -> i64 { return 1; }\nfn test() -> i64 { let p: P = P { x: 1 }; let q: i64 = use_it(p); return q; }\n",
        &["test(F)", "use_it__P(F)"],
    ),
    // A generic-record type-arg: the NESTED mangle.
    (
        "p_generic_record_targ",
        "module m;\nrecord BoxG<T> { v: T }\nfn use_it<T>(x: T) -> i64 { return 1; }\nfn test() -> i64 { let b: BoxG<i64> = BoxG { v: 5 }; let c: i64 = use_it(b); return c; }\n",
        &["test(F)", "use_it__BoxG__i64(F)"],
    ),
    // A 3-deep transitive chain: post-order (deepest first), well inside
    // MAX_MONOMORPH_DEPTH = 64 (types.rs:716).
    (
        "p_chain3",
        "module m;\nfn f1<T>(x: T) -> T { return x; }\nfn f2<T>(x: T) -> T { let y = f1(x); return y; }\nfn f3<T>(x: T) -> T { let y = f2(x); return y; }\nfn test() -> i64 { let a: i64 = f3(5); return a; }\n",
        &["test(F)", "f1__i64(F)", "f2__i64(F)", "f3__i64(F)"],
    ),
    // Monomorphic self-recursion inside a generic: registers ONCE (the cache breaks the cycle).
    (
        "p_self_recursive",
        "module m;\nfn r<T>(x: T) -> T { let y = r(x); return y; }\nfn test() -> i64 { let a: i64 = r(5); return a; }\n",
        &["test(F)", "r__i64(F)"],
    ),
    // A generic impl method: {Type}__{method}__{targs}.
    (
        "p_impl_method",
        "module m;\nrecord BoxG<T> { v: T }\nimpl BoxG<T> { pub fn get(self: BoxG<T>) -> T { return self.v; } }\nfn test() -> i64 { let b: BoxG<i64> = BoxG { v: 5 }; let r: i64 = b.get(); return r; }\n",
        &["test(F)", "BoxG__get__i64(F)"],
    ),
    // A generic-enum construction creates NO fn instance (layout only — see the layout pin).
    (
        "p_generic_enum",
        "module m;\nenum OptG<T> { SomeV(T), NoneV }\nfn test() -> i64 { let o: OptG<i64> = OptG::SomeV(5); return 1; }\n",
        &["test(F)"],
    ),
];

/// The ordered census pins — the ground truth the MONO-1+ shadow must reproduce.
#[test]
fn mono0_census_pins() {
    for (label, src, want) in MONO_CENSUS_PINS {
        let got = oracle_functions(label, src)
            .unwrap_or_else(|codes| panic!("SH-MONO {label}: expected type-clean, got {codes:?}"));
        assert_eq!(
            got,
            want.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
            "SH-MONO {label}: the oracle instance census drifted\n{src}"
        );
    }
}

/// THE LAYOUT ASYMMETRY PIN: a constructed generic ENUM registers a concrete layout key
/// (`OptG__i64`, via register_concrete_enum resolve.rs:521) but a constructed generic RECORD
/// does NOT (records keep only the generic base `BoxG`) — the MONO-2 layout-census lane must
/// mirror exactly this, not a symmetric guess.
#[test]
fn mono0_layout_asymmetry() {
    let rec_src = "module m;\nrecord BoxG<T> { v: T }\nfn use_it<T>(x: T) -> i64 { return 1; }\nfn test() -> i64 { let b: BoxG<i64> = BoxG { v: 5 }; let c: i64 = use_it(b); return c; }\n";
    let (recs, enums) = oracle_layout_keys("layout_record", rec_src);
    assert_eq!(recs, vec!["BoxG".to_string()], "no concrete record key");
    assert!(enums.is_empty());

    let enum_src = "module m;\nenum OptG<T> { SomeV(T), NoneV }\nfn test() -> i64 { let o: OptG<i64> = OptG::SomeV(5); return 1; }\n";
    let (recs2, enums2) = oracle_layout_keys("layout_enum", enum_src);
    assert!(recs2.is_empty());
    assert_eq!(
        enums2,
        vec!["OptG".to_string(), "OptG__i64".to_string()],
        "the generic base AND the concrete instance"
    );
}

/// AG-M6: the polymorphic-recursion path is LOUD — it rejects (here on the pre-depth
/// type errors; the MAX_MONOMORPH_DEPTH=64 guard sits behind them), never silently accepts.
#[test]
fn mono0_poly_recursion_rejects_loud() {
    let src = "module m;\nrecord BoxG<T> { v: T }\nfn rec<T>(x: T) -> i64 { let b: BoxG<T> = BoxG { v: x }; let r: i64 = rec(b); return r; }\nfn test() -> i64 { let a: i64 = rec(5); return a; }\n";
    let out = oracle_functions("p_poly_recursion", src);
    let codes = out.expect_err("polymorphic recursion must reject, not silently accept");
    assert!(!codes.is_empty(), "reject carries diagnostic codes");
}

/// Determinism: the census extraction is stable across runs.
#[test]
fn mono0_oracle_deterministic() {
    for (label, src, _) in MONO_CENSUS_PINS {
        assert_eq!(
            oracle_functions(label, src),
            oracle_functions(label, src),
            "SH-MONO {label}: oracle census must be deterministic"
        );
    }
}

// ── MONO-1: the selfhost census shadow (`mn_census`) — the sorted-list differential ─────────
//
// The shadow (selfhost/monomorph.sigil) reproduces the oracle's function census over the v1
// surface (single module, free generic fns, bare-T params, scalar/plain-record type-args,
// calls from monomorphic bodies). It emits WALK order (X-M8) and the
// harness compares SORTED — order becomes load-bearing at MONO-3.

/// Strip a module's `\nmodule X;\n` header so it composes into `module tool;`.
fn strip_module(src: &str, name: &str) -> String {
    src.replace(&format!("\nmodule {name};\n"), "\n")
}

/// The census-shadow tool: lexer + parser + typecheck + monomorph composed (standalone — the
/// sh_compile mega-tool is NOT involved; composition into it is MONO-4).
fn mn_tool() -> String {
    let lexer = strip_module(include_str!("../../../selfhost/lexer.sigil"), "lexer");
    let parser_s = strip_module(include_str!("../../../selfhost/parser.sigil"), "parser");
    let tc = strip_module(
        include_str!("../../../selfhost/typecheck.sigil"),
        "typecheck",
    );
    let mn = strip_module(
        include_str!("../../../selfhost/monomorph.sigil"),
        "monomorph",
    );
    format!(
        "module tool;\n{lexer}\n{parser_s}\n{tc}\n{mn}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n    let opt: Option<str> = input_ptr.from_bytes(input_len);\n    let src: str = opt.unwrap_or(\"\");\n    let toks: Vec<Token> = lex(src);\n    let mut nodes: Arena<PNode> = Arena::new();\n    let mut kids: Vec<i64> = Vec::new();\n    let root: i64 = parser_parse(src, toks, nodes, kids);\n    let enc: str = mn_census(nodes, kids, root);\n    let lay: str = mn_layouts(nodes, kids, root);\n    let bar: str = \"|\";\n    let withbar: str = enc.concat(bar);\n    let full: str = withbar.concat(lay);\n    return full.as_output();\n}}\n"
    )
}

fn mn_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        sigil_compiler::compile_tool(&mn_tool())
            .expect("the mn census tool should compile")
            .wasm
    })
}

/// Run the shadow census; returns the SORTED name list.
fn mn_census_out(src: &str) -> Vec<String> {
    let result = sigil_runtime::execute_ephemeral(
        mn_wasm(),
        src.as_bytes(),
        EXECUTION_FUEL,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the mn census tool executes");
    let out = String::from_utf8(result.output).expect("census output is UTF-8");
    let census = out.split('|').next().unwrap_or("");
    let mut v: Vec<String> = census
        .split(';')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect();
    v.sort();
    v
}

/// Run the shadow and return the LAYOUT sections (records, enums), each sorted.
fn mn_layout_out(src: &str) -> (Vec<String>, Vec<String>) {
    let result = sigil_runtime::execute_ephemeral(
        mn_wasm(),
        src.as_bytes(),
        EXECUTION_FUEL,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the mn census tool executes");
    let out = String::from_utf8(result.output).expect("census output is UTF-8");
    let mut secs = out.split('|');
    let _census = secs.next();
    let parse = |seg: Option<&str>| -> Vec<String> {
        let mut v: Vec<String> = seg
            .unwrap_or("")
            .split(';')
            .filter(|s| !s.is_empty())
            .map(|s| s.to_string())
            .collect();
        v.sort();
        v
    };
    (parse(secs.next()), parse(secs.next()))
}

/// The oracle census as a SORTED bare-name list (the `(kind)` suffix stripped).
fn oracle_names(label: &str, src: &str) -> Vec<String> {
    let fns = oracle_functions(label, src).unwrap_or_else(|codes| {
        panic!("MONO-1 {label}: fixture must be type-clean, got {codes:?}")
    });
    let mut v: Vec<String> = fns
        .iter()
        .map(|s| s.split('(').next().unwrap_or(s).to_string())
        .collect();
    v.sort();
    v
}

/// The MONO-1 v1 corpus: single-module, bare-T free generics, calls from monomorphic bodies.
/// (Transitive-from-generic-bodies, impl methods, generic-record targs, rettp-via-expected and
/// multi-module are fenced to the transitive-expansion corpus.)
const MONO1_CORPUS: &[(&str, &str)] = &[
    (
        "d_min",
        "module m;\nfn id<T>(x: T) -> T { return x; }\nfn test() -> i64 { let a: i64 = id(5); let b: bool = id(true); return a; }\n",
    ),
    (
        "d_dedup",
        "module m;\nfn id<T>(x: T) -> T { return x; }\nfn test() -> i64 { let a: i64 = id(5); let b: i64 = id(6); return a + b; }\n",
    ),
    (
        "d_uncalled",
        "module m;\nfn id<T>(x: T) -> T { return x; }\nfn test() -> i64 { return 7; }\n",
    ),
    (
        "d_nested",
        "module m;\nfn wrap<T>(x: T) -> T { return x; }\nfn id<T>(x: T) -> T { return x; }\nfn test() -> i64 { let a: i64 = id(wrap(5)); return a; }\n",
    ),
    (
        "d_two_generics",
        "module m;\nfn ga<T>(x: T) -> T { return x; }\nfn gb<T>(x: T) -> T { return x; }\nfn test() -> i64 { let s: str = \"x\"; let b: str = gb(s); let a: i64 = ga(1); return a; }\n",
    ),
    (
        "d_mixed_annotated",
        "module m;\nfn id2<T>(a: T, b: T) -> T { return a; }\nfn test(x: u32) -> u32 { let r: u32 = id2(5, x); return r; }\n",
    ),
    (
        "d_mixed_concrete_first",
        "module m;\nfn id2<T>(a: T, b: T) -> T { return a; }\nfn test(x: u32) -> u32 { let r: u32 = id2(x, 5); return r; }\n",
    ),
    (
        "d_pair",
        "module m;\nfn pair<A, B>(a: A, b: B) -> A { return a; }\nfn test() -> i64 { let s: str = \"x\"; let r: i64 = pair(7, s); return r; }\n",
    ),
    (
        "d_record_targ",
        "module m;\nrecord P { x: i64 }\nfn use_it<T>(x: T) -> i64 { return 1; }\nfn test() -> i64 { let p: P = P { x: 1 }; let q: i64 = use_it(p); return q; }\n",
    ),
    (
        "d_self_recursive",
        "module m;\nfn r<T>(x: T) -> T { let y = r(x); return y; }\nfn test() -> i64 { let a: i64 = r(5); return a; }\n",
    ),
    (
        "d_cf_dedup",
        "module m;\nfn id<T>(x: T) -> T { return x; }\nfn test(n: i64) -> i64 { let mut s: i64 = 0; if n > 0 { let a: i64 = id(1); s = s + a; } else { } while s < n { let b: i64 = id(2); s = s + b; } return s; }\n",
    ),
    // Folded sweep permanents (8/8 sweep, 2026-07-12): the first-binding-wins CONFLICT
    // (T binds the literal, the later str arg does not override — stronger than either
    // discriminator), a generic call inside a MONO call's args, the unannotated-let bind
    // chain, and a construct-as-arg.
    (
        "d_conflict_lit_then_str",
        "module m;
fn id2<T>(a: T, b: T) -> T { return a; }
fn test(s: str) -> i64 { let r = id2(1, s); return 0; }
",
    ),
    (
        "d_generic_in_mono_arg",
        "module m;
fn id<T>(x: T) -> T { return x; }
fn g(x: i64) -> i64 { return x + 1; }
fn test() -> i64 { let a: i64 = g(id(5)); return a; }
",
    ),
    (
        "d_unannotated_let_chain",
        "module m;
fn id<T>(x: T) -> T { return x; }
fn test() -> i64 { let a = id(5); let b: i64 = id(a); return b; }
",
    ),
    (
        "d_construct_arg",
        "module m;
record P { x: i64 }
fn use_it<T>(x: T) -> i64 { return 1; }
fn test() -> i64 { let q: i64 = use_it(P { x: 1 }); return q; }
",
    ),
    (
        "d_three_types",
        "module m;\nfn id<T>(x: T) -> T { return x; }\nfn test() -> i64 { let a: i64 = id(5); let b: bool = id(true); let s: str = \"x\"; let c: str = id(s); return a; }\n",
    ),
];

/// MONO-1: the shadow census equals the oracle census (sorted) over the v1 corpus.
#[test]
fn mono1_census_parity() {
    for (label, src) in MONO1_CORPUS {
        assert_eq!(
            mn_census_out(src),
            oracle_names(label, src),
            "MONO-1 {label}: the census shadow diverged\n{src}"
        );
    }
}

/// Non-stub (X-M5): the exact pinned lists, counts included — a stub emitting only the
/// monomorphic fns (or hardcoding __i64) fails by name.
#[test]
fn mono1_non_stub_pins() {
    assert_eq!(
        mn_census_out(MONO1_CORPUS[0].1),
        vec!["id__bool", "id__i64", "test"],
        "d_min exact census"
    );
    assert_eq!(
        mn_census_out(MONO1_CORPUS[7].1),
        vec!["pair__i64$str", "test"],
        "d_pair exact census ($-join)"
    );
    assert_eq!(
        mn_census_out(MONO1_CORPUS[5].1),
        vec!["id2__i64", "test"],
        "the X-M7 discriminator: the literal binds T first"
    );
    assert_eq!(
        mn_census_out(MONO1_CORPUS[6].1),
        vec!["id2__u32", "test"],
        "the X-M7 discriminator: the concrete binds T first"
    );
}

/// Determinism: two runs produce identical census lists.
#[test]
fn mono1_deterministic() {
    for (label, src) in MONO1_CORPUS {
        assert_eq!(
            mn_census_out(src),
            mn_census_out(src),
            "MONO-1 {label}: the shadow census must be deterministic"
        );
    }
}

// ── MONO-2: census breadth — transitive, impl methods, the layout lane ──────────────────────

/// The MONO-2 corpus: the transitive-instantiation surface
/// from generic bodies (unannotated lets, the T046 discipline), generic impl-method instances
/// via let-bound receivers, method-body transitivity, concrete-impl monos.
const MONO2_CORPUS: &[(&str, &str)] = &[
    (
        "t_transitive_subst",
        "module m;\nfn inner<T>(x: T) -> T { return x; }\nfn outer<T>(x: T) -> T { let y = inner(x); return y; }\nfn test() -> bool { let a: bool = outer(true); return a; }\n",
    ),
    (
        "t_transitive_two",
        "module m;\nfn inner<T>(x: T) -> T { return x; }\nfn outer<T>(x: T) -> T { let y = inner(x); return y; }\nfn test() -> i64 { let a: i64 = outer(5); let b: bool = outer(true); return a; }\n",
    ),
    (
        "t_transitive_concrete",
        "module m;\nfn inner<T>(x: T) -> T { return x; }\nfn outer<T>(x: T) -> T { let z = inner(1); return x; }\nfn test() -> bool { let a: bool = outer(true); return a; }\n",
    ),
    (
        "t_chain3",
        "module m;\nfn f1<T>(x: T) -> T { return x; }\nfn f2<T>(x: T) -> T { let y = f1(x); return y; }\nfn f3<T>(x: T) -> T { let y = f2(x); return y; }\nfn test() -> i64 { let a: i64 = f3(5); return a; }\n",
    ),
    (
        "t_impl_method",
        "module m;\nrecord BoxG<T> { v: T }\nimpl BoxG<T> { pub fn get(self: BoxG<T>) -> T { return self.v; } }\nfn test() -> i64 { let b: BoxG<i64> = BoxG { v: 5 }; let r: i64 = b.get(); return r; }\n",
    ),
    (
        "t_impl_method_two",
        "module m;\nrecord BoxG<T> { v: T }\nimpl BoxG<T> { pub fn get(self: BoxG<T>) -> T { return self.v; } }\nfn test() -> i64 { let b: BoxG<i64> = BoxG { v: 5 }; let c: BoxG<bool> = BoxG { v: true }; let r: i64 = b.get(); let s: bool = c.get(); return r; }\n",
    ),
    (
        "t_method_transitive",
        "module m;\nrecord BoxG<T> { v: T }\nfn idg<T>(x: T) -> T { return x; }\nimpl BoxG<T> { pub fn get(self: BoxG<T>) -> T { let w = idg(self.v); return w; } }\nfn test() -> i64 { let b: BoxG<i64> = BoxG { v: 5 }; let r: i64 = b.get(); return r; }\n",
    ),
    // Folded sweep permanents (6/6 x 2 lanes, 2026-07-12): method-from-method (the self
    // bind's targs flow into a second method instance), a 2-tp instance created TRANSITIVELY
    // with mixed bindings (subst env + local), the PR-G3b param-receiver path, and a
    // local-payload enum key.
    (
        "t_method_from_method",
        "module m;
record BoxG<T> { v: T }
impl BoxG<T> { pub fn raw(self: BoxG<T>) -> T { return self.v; } pub fn get(self: BoxG<T>) -> T { let w = self.raw(); return w; } }
fn test() -> i64 { let b: BoxG<i64> = BoxG { v: 5 }; let r: i64 = b.get(); return r; }
",
    ),
    (
        "t_two_tp_transitive",
        "module m;
fn id2<A, B>(a: A, b: B) -> A { return a; }
fn outer<T>(x: T) -> T { let s: str = \"k\"; let y = id2(x, s); return y; }
fn test() -> bool { let a: bool = outer(true); return a; }
",
    ),
    (
        "t_param_receiver",
        "module m;
record BoxG<T> { v: T }
impl BoxG<T> { pub fn get(self: BoxG<T>) -> T { return self.v; } }
fn use_box(b: BoxG<i64>) -> i64 { let r: i64 = b.get(); return r; }
fn test() -> i64 { let b: BoxG<i64> = BoxG { v: 5 }; let r: i64 = use_box(b); return r; }
",
    ),
    (
        "t_concrete_impl",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\nfn test() -> i64 { let p: P = P { x: 1 }; let r: i64 = p.get(); return r; }\n",
    ),
    (
        "t_concrete_impl_calls_generic",
        "module m;\nrecord P { x: i64 }\nfn idg<T>(x: T) -> T { return x; }\nimpl P { pub fn get(self: P) -> i64 { let w: i64 = idg(self.x); return w; } }\nfn test() -> i64 { let p: P = P { x: 1 }; let r: i64 = p.get(); return r; }\n",
    ),
];

/// MONO-2: the shadow census equals the oracle census (sorted) over the v2 corpus.
#[test]
fn mono2_census_parity() {
    for (label, src) in MONO2_CORPUS {
        assert_eq!(
            mn_census_out(src),
            oracle_names(label, src),
            "MONO-2 {label}: the census shadow diverged\n{src}"
        );
    }
}

/// Non-stub: exact pinned lists for the sharpest v2 shapes.
fn mono2_src(label: &str) -> &'static str {
    MONO2_CORPUS.iter().find(|(l, _)| *l == label).unwrap().1
}

#[test]
fn mono2_non_stub_pins() {
    assert_eq!(
        mn_census_out(mono2_src("t_transitive_two")),
        vec![
            "inner__bool",
            "inner__i64",
            "outer__bool",
            "outer__i64",
            "test"
        ],
        "t_transitive_two exact census"
    );
    assert_eq!(
        mn_census_out(mono2_src("t_method_transitive")),
        vec!["BoxG__get__i64", "idg__i64", "test"],
        "t_method_transitive exact census"
    );
    assert_eq!(
        mn_census_out(mono2_src("t_concrete_impl")),
        vec!["P__get", "test"],
        "t_concrete_impl exact census"
    );
    assert_eq!(
        mn_census_out(mono2_src("t_two_tp_transitive")),
        vec!["id2__bool$str", "outer__bool", "test"],
        "t_two_tp_transitive exact census (the folded mixed-binding instance)"
    );
}

/// The layout lane: records never get concrete keys; a payload-driven generic-enum ctor
/// registers `{Enum}__{targ}` (the MONO-0/2 asymmetry pins).
#[test]
fn mono2_layout_parity() {
    let cases: &[(&str, &str)] = &[
        (
            "l_enum_payload",
            "module m;\nenum OptG<T> { SomeV(T), NoneV }\nfn test() -> i64 { let o = OptG::SomeV(5); return 1; }\n",
        ),
        (
            "l_enum_annotated",
            "module m;\nenum OptG<T> { SomeV(T), NoneV }\nfn test() -> i64 { let o: OptG<i64> = OptG::SomeV(5); return 1; }\n",
        ),
        (
            "l_record_no_key",
            "module m;\nrecord BoxG<T> { v: T }\nfn use_it<T>(x: T) -> i64 { return 1; }\nfn test() -> i64 { let b: BoxG<i64> = BoxG { v: 5 }; let c: i64 = use_it(b); return c; }\n",
        ),
        (
            "l_enum_local_payload",
            "module m;
enum OptG<T> { SomeV(T), NoneV }
fn test(f: bool) -> i64 { let o = OptG::SomeV(f); return 1; }
",
        ),
        (
            "l_enum_uncalled",
            "module m;
enum OptG<T> { SomeV(T), NoneV }
fn test() -> i64 { return 1; }
",
        ),
        (
            "l_mixed",
            "module m;\nrecord P { x: i64 }\nenum OptG<T> { SomeV(T), NoneV }\nfn test() -> bool { let p: P = P { x: 1 }; let o = OptG::SomeV(true); return true; }\n",
        ),
    ];
    for (label, src) in cases {
        let (srec, senum) = mn_layout_out(src);
        let (orec, oenum) = oracle_layout_keys(label, src);
        assert_eq!(srec, orec, "MONO-2 {label}: records layout diverged");
        assert_eq!(senum, oenum, "MONO-2 {label}: enums layout diverged");
    }
}

/// Determinism over the v2 corpus.
#[test]
fn mono2_deterministic() {
    for (label, src) in MONO2_CORPUS {
        assert_eq!(
            mn_census_out(src),
            mn_census_out(src),
            "MONO-2 {label}: the shadow census must be deterministic"
        );
    }
}

// ── MONO-3 Phase-0: the byte-target feasibility probe ────────────────────────────────────────

use sigil_compiler::air;
use sigil_compiler::fuel;
use sigil_compiler::memory;
use sigil_compiler::wasm;

/// The oracle W-lane byte target for a whole tool: parse -> resolve -> type_check (monomorphizes)
/// -> air::lower -> memory -> fuel -> wasm::emit, as lowercase hex.
fn oracle_wasm_hex(label: &str, src: &str) -> String {
    let source = SourceFile::new("<mono-wasm>", src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(pdiags.is_empty(), "MONO-3 {label}: parse-clean");
    let resolved = name_resolution::resolve(&ast).expect("resolve");
    let (typed, _) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .unwrap_or_else(|ds| {
            panic!(
                "MONO-3 {label}: tc {:?}",
                ds.iter().map(|d| d.code().to_string()).collect::<Vec<_>>()
            )
        });
    let lowered = air::lower(&typed);
    let (mem_p, _) = memory::lower(lowered);
    let (fuel_p, _) = fuel::insert(mem_p);
    let out = wasm::emit(&fuel_p);
    assert!(out.outer.is_none(), "MONO-3 {label}: single-ring");
    out.inner.iter().map(|b| format!("{b:02x}")).collect()
}

// ── MONO-3: mn_expand — the execution capstone + code-section byte identity ──────────────────

/// The expand tool: lexer+parser+typecheck+air+monomorph composed; body = lex -> parse ->
/// mn_expand (monomorphize in place) -> ai_encode_wasm (the existing W-lane).
fn mnexp_tool() -> String {
    let lexer = strip_module(include_str!("../../../selfhost/lexer.sigil"), "lexer");
    let parser_s = strip_module(include_str!("../../../selfhost/parser.sigil"), "parser");
    let tc = strip_module(
        include_str!("../../../selfhost/typecheck.sigil"),
        "typecheck",
    );
    let air_s = strip_module(include_str!("../../../selfhost/air.sigil"), "air");
    let mn = strip_module(
        include_str!("../../../selfhost/monomorph.sigil"),
        "monomorph",
    );
    format!(
        "module tool;\n{lexer}\n{parser_s}\n{tc}\n{air_s}\n{mn}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n    let opt: Option<str> = input_ptr.from_bytes(input_len);\n    let src: str = opt.unwrap_or(\"\");\n    let toks: Vec<Token> = lex(src);\n    let mut nodes: Arena<PNode> = Arena::new();\n    let mut kids: Vec<i64> = Vec::new();\n    let root: i64 = parser_parse(src, toks, nodes, kids);\n    let e: i64 = mn_expand(nodes, kids, root);\n    let hex: str = ai_encode_wasm(nodes, kids, root);\n    return hex.as_output();\n}}\n"
    )
}

fn mnexp_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        sigil_compiler::compile_tool(&mnexp_tool())
            .expect("the mn_expand tool should compile")
            .wasm
    })
}

fn mnexp_hex(src: &str) -> String {
    let result = sigil_runtime::execute_ephemeral(
        mnexp_wasm(),
        src.as_bytes(),
        EXECUTION_FUEL,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the mn_expand tool executes");
    String::from_utf8(result.output).expect("hex is UTF-8")
}

/// Extract the CODE section (id 0x0A) body bytes from a wasm module hex, by section walk.
fn code_section(hex: &str) -> Vec<u8> {
    let b: Vec<u8> = (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex"))
        .collect();
    let mut p = 8usize; // skip magic + version
    while p < b.len() {
        let id = b[p];
        p += 1;
        // read uleb section length
        let mut len = 0u64;
        let mut shift = 0;
        loop {
            let byte = b[p];
            p += 1;
            len |= ((byte & 0x7f) as u64) << shift;
            if byte & 0x80 == 0 {
                break;
            }
            shift += 7;
        }
        let len = len as usize;
        if id == 0x0a {
            return b[p..p + len].to_vec();
        }
        p += len;
    }
    Vec::new()
}

/// The MONO-3 expand corpus: whole `module tool;` programs, generic source + a tool_main that
/// calls it. The oracle monomorphizes; mn_expand expands the same tree; the CODE sections must
/// be byte-identical (bodies + FuncId call indices). Whole-module identity awaits MONO-3b (the
/// bare-instance-export extension), so we compare the code section here.
const MONO3_CORPUS: &[(&str, &str)] = &[
    (
        "c_id",
        "module tool;\nfn id<T>(x: T) -> T { return x; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = id(25); let b: i64 = id(16); return 0 - (a + b); }\n",
    ),
    (
        "c_two_types",
        "module tool;\nfn id<T>(x: T) -> T { return x; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = id(25); let f: bool = id(true); let b: i64 = id(16); return 0 - (a + b); }\n",
    ),
    (
        "c_id2",
        "module tool;\nfn id2<T>(a: T, b: T) -> T { return a; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let r: i64 = id2(25, 16); return 0 - r; }\n",
    ),
    (
        "c_pair",
        "module tool;\nfn pair<A, B>(a: A, b: B) -> A { return a; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let r: i64 = pair(41, true); return 0 - r; }\n",
    ),
    (
        "c_str_and_i64",
        "module tool;\nfn id<T>(x: T) -> T { return x; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let s: str = id(\"k\"); let a: i64 = id(41); return 0 - a; }\n",
    ),
    // Folded sweep permanents (6/6, 2026-07-12): y_nested_call caught the inline-patch bug
    // (an enclosing call typed its arg against a not-yet-known instance sig) -> the deferred
    // patch-list restructure. Plus many-instance dedup and two distinct generics.
    (
        "c_nested_call",
        "module tool;
fn id<T>(x: T) -> T { return x; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = id(id(41)); return 0 - a; }
",
    ),
    (
        "c_dedup_many",
        "module tool;
fn id<T>(x: T) -> T { return x; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = id(1); let b: i64 = id(2); let c: i64 = id(3); let d: bool = id(true); let e: bool = id(false); return 0 - (a + b + c); }
",
    ),
    (
        "c_two_generics",
        "module tool;
fn ga<T>(x: T) -> T { return x; }
fn gb<T>(x: T) -> T { return x; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = ga(20); let b: i64 = gb(21); return 0 - (a + b); }
",
    ),
    (
        "c_cf",
        "module tool;\nfn id<T>(x: T) -> T { return x; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < 3 { let d: i64 = id(i); s = s + d; i = i + 1; } if s > 0 { let e: i64 = id(100); s = s + e; } else { } return 0 - s; }\n",
    ),
];

/// The real-monomorphizer proof: mn_expand's output CODE section == the oracle's, byte-identical,
/// over the whole corpus. (Whole-module identity = MONO-3b; the export section is the only delta.)
#[test]
fn mono3_code_section_parity() {
    for (label, src) in MONO3_CORPUS {
        let oracle = code_section(&oracle_wasm_hex(label, src));
        let shadow = code_section(&mnexp_hex(src));
        assert!(
            !oracle.is_empty(),
            "MONO-3 {label}: oracle has a code section"
        );
        assert_eq!(
            oracle, shadow,
            "MONO-3 {label}: mn_expand's monomorphized code section diverged\n{src}"
        );
    }
}

/// Decode a wasm hex to bytes.
fn hex_bytes(hex: &str) -> Vec<u8> {
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex"))
        .collect()
}

fn assert_module_parity<S: AsRef<str>>(lane: &str, corpus: &[(&str, S)]) {
    for (label, source) in corpus {
        let source = source.as_ref();
        assert_eq!(
            oracle_wasm_hex(label, source),
            mnexp_hex(source),
            "{lane} {label}: whole-module byte identity\n{source}"
        );
    }
}

fn assert_corpus_deterministic<S: AsRef<str>>(lane: &str, corpus: &[(&str, S)]) {
    for (label, source) in corpus {
        let source = source.as_ref();
        assert_eq!(
            mnexp_hex(source),
            mnexp_hex(source),
            "{lane} {label}: deterministic expansion"
        );
    }
}

fn corpus_source<'a, S: AsRef<str>>(corpus: &'a [(&str, S)], label: &str) -> &'a str {
    corpus
        .iter()
        .find(|(candidate, _)| *candidate == label)
        .map(|(_, source)| source.as_ref())
        .unwrap_or_else(|| panic!("missing corpus case {label}"))
}

fn assert_execution_magnitude(lane: &str, label: &str, source: &str, magnitude: i64) {
    let oracle = oracle_wasm_hex(label, source);
    let shadow = mnexp_hex(source);
    assert_eq!(oracle, shadow, "{lane}: capstone modules byte-identical");

    let module = hex_bytes(&shadow);
    let run = sigil_runtime::execute_ephemeral(
        &module,
        b"",
        EXECUTION_FUEL,
        &sigil_runtime::grants::IoGrants::none(),
    );
    let output = format!("{run:?}");
    assert!(
        output.contains(&magnitude.to_string()),
        "{lane}: expected negative-sentinel magnitude {magnitude}, got {output}"
    );
}

/// The execution capstone: a generic program monomorphized BY mn_expand compiles to a module
/// that RUNS to the same value as the oracle-compiled generic program — the end-to-end
/// "pure-SIGIL monomorphizer produces running code" proof.
#[test]
fn mono3_execution_capstone() {
    let generic = MONO3_CORPUS[0].1; // c_id: 0 - (id(25) + id(16)) = -41
    let oracle_mod = hex_bytes(&oracle_wasm_hex("cap", generic));
    let shadow_mod = hex_bytes(&mnexp_hex(generic));

    let run = |m: &[u8]| -> String {
        match sigil_runtime::execute_ephemeral(
            m,
            b"",
            EXECUTION_FUEL,
            &sigil_runtime::grants::IoGrants::none(),
        ) {
            Err(sigil_runtime::ToolError::Trapped { message }) => message,
            other => panic!("expected the neg-sentinel trap, got {other:?}"),
        }
    };
    let oracle_run = run(&oracle_mod);
    let shadow_run = run(&shadow_mod);
    assert!(
        shadow_run.contains("tool returned error (41)"),
        "the mn_expand-compiled generic program must return -41: {shadow_run}"
    );
    assert_eq!(
        shadow_run, oracle_run,
        "the mn_expand-compiled module must run identically to the oracle-compiled one"
    );
}

/// Clone hygiene (X-M10): two instances of the same generic at DIFFERENT types must both compile
/// correctly — if the clones shared kids ranges, one would corrupt the other, breaking the code
/// section. (The strongest observable proxy for the fresh-range invariant through the tool.)
#[test]
fn mono3_clone_hygiene() {
    let src = MONO3_CORPUS[1].1; // c_two_types: id__i64 + id__bool
    let oracle = code_section(&oracle_wasm_hex("hygiene", src));
    let shadow = code_section(&mnexp_hex(src));
    assert_eq!(
        oracle, shadow,
        "two same-generic instances at different types must not corrupt each other's clones"
    );
}

/// Determinism: two expand runs produce the identical module.
#[test]
fn mono3_deterministic() {
    assert_corpus_deterministic("MONO-3", MONO3_CORPUS);
}

// ── MONO-3b: whole-module byte identity (the bare-instance-export closes the last gap) ───────

/// MONO-3b: with the W-lane exporting monomorphized instances under their BARE mangled name,
/// mn_expand's WHOLE-MODULE wasm is byte-identical to the oracle's over the generic corpus —
/// not just the code section. This is the plan's original X-B3 whole-module byte criterion.
#[test]
fn mono3b_whole_module_parity() {
    assert_module_parity("MONO-3b", MONO3_CORPUS);
}

// ── MONO-5: transitive-body expansion — the clone-first recursive engine ────────────────────
//
// mn_expand's engine (MONO-5) clones a freshly-resolved instance IMMEDIATELY and recursively
// walks the CLONE's body (concrete params -> plain tc_seed_params; clone-local node ids -> its
// deferred patch list applies directly, X-E2), so inner instances append themselves FIRST —
// the oracle's post-order (cache-before-check) falls out of the recursion (X-E1, ONE engine).
// Phase-0 pinned the oracle order live: chain3 = [f3,f2,f1] deepest-first; the diamond dedups
// inner at its FIRST-discovery position; a self-recursive generic registers ONCE (the pre-order
// seen-mark breaks the cycle); a transitive 2-tp callee lands before its discoverer.
//
// Corpus note (Phase-0 find): instance bodies flow through the SAME W-lane covered subset as
// any fn body — an out-of-subset form (e.g. an unannotated let) poisons LOUD exactly as it
// would in a mono body; the corpus uses let-free generic bodies. Nothing new is fenced by
// MONO-5 itself.
const MONO5_CORPUS: &[(&str, &str)] = &[
    (
        "t5_chain3",
        "module tool;
fn f3<T>(x: T) -> T { return x; }
fn f2<T>(x: T) -> T { return f3(x); }
fn f1<T>(x: T) -> T { return f2(x); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = f1(41); return 0 - a; }
",
    ),
    (
        "t5_diamond",
        "module tool;
fn inner<T>(x: T) -> T { return x; }
fn outa<T>(x: T) -> T { return inner(x); }
fn outb<T>(x: T) -> T { return inner(inner(x)); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = outa(20); let b: i64 = outb(21); return 0 - (a + b); }
",
    ),
    (
        "t5_selfrec",
        "module tool;
fn rec<T>(x: T, n: i64) -> T { if n > 0 { return rec(x, n - 1); } else { } return x; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = rec(41, 3); return 0 - a; }
",
    ),
    // Folded sweep permanents (5/5 green, 2026-07-13): the per-root two-type interleave (the
    // strongest order fixture), the enclosing-call-inside-a-clone (the X-E2 per-clone deferred
    // patch shape), and a clone body calling a MONO fn (mixed callee resolution, unpatched).
    (
        "t5_two_type_interleave",
        "module tool;
fn inner<T>(x: T) -> T { return x; }
fn outer<T>(x: T) -> T { return inner(x); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = outer(41); let b: bool = outer(true); return 0 - a; }
",
    ),
    (
        "t5_nested_in_clone",
        "module tool;
fn leaf<T>(x: T) -> T { return x; }
fn h<T>(x: T) -> T { return leaf(leaf(x)); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = h(41); return 0 - a; }
",
    ),
    (
        "t5_clone_calls_mono",
        "module tool;
fn m(k: i64) -> i64 { return k + 1; }
fn g<T>(x: T) -> i64 { return m(7); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = g(true); return 0 - a; }
",
    ),
    (
        "t5_mixed_tp",
        "module tool;
fn id2<A, B>(a: A, b: B) -> A { return a; }
fn outer<T>(x: T) -> T { return id2(x, true); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = outer(41); return 0 - a; }
",
    ),
];

/// MONO-5: whole-module byte identity over the transitive corpus — the expanded tree (instances
/// cloned + appended post-order + call sites patched, transitively) emits the SAME bytes as the
/// oracle compiling the generic source.
#[test]
fn mono5_whole_module_parity() {
    assert_module_parity("MONO-5", MONO5_CORPUS);
}

/// X-E1b (conservation): the census and the expansion engines agree on the instance SET —
/// mn_census's instances == the oracle's instance list (bare tails). Combined with
/// mono5_whole_module_parity (expansion == oracle, bytes), census == expansion transitively.
#[test]
fn mono5_census_expansion_conservation() {
    for (label, src) in MONO5_CORPUS {
        let mut census: Vec<String> = mn_census_out(src)
            .into_iter()
            .filter(|n| n.contains("__"))
            .collect();
        census.sort();
        let mut oracle: Vec<String> = oracle_functions(label, src)
            .expect("accept fixture")
            .into_iter()
            .filter(|n| n.contains("__"))
            .map(|n| n.trim_end_matches("(F)").to_string())
            .collect();
        oracle.sort();
        assert_eq!(
            census, oracle,
            "MONO-5 {label}: census/expansion drift (instance sets)"
        );
    }
}

/// MONO-5 execution capstone: a 3-deep transitive generic program monomorphized BY mn_expand
/// runs to the same value as the oracle-compiled module.
#[test]
fn mono5_execution_capstone() {
    let generic = MONO5_CORPUS[0].1; // t5_chain3: 0 - f1(41) = -41
    assert_execution_magnitude("MONO-5", "cap5", generic, 41);
}

/// MONO-5 determinism: the expansion is a pure function of the source.
#[test]
fn mono5_deterministic() {
    assert_corpus_deterministic("MONO-5", MONO5_CORPUS);
}

// ── MONO-6: generic-record expansion — concrete def clones + 0-child annotation rewrites ────
//
// mn_expand (after fn expansion) clones a concrete P_K_RECORD_DEF per generic-record
// instantiation and rewrites each `Box<i64>` annotation to a 0-child `Box__i64` leaf, so the
// W-lane's tc_type_topcode resolves the binding and `b.v` field reads/writes find offsets.
// Constructs need NO rewrite (every scalar/pointer is width 8, so the generic def's construct
// layout already matches the oracle's concrete instantiation). The instance mangle is
// SHADOW-INTERNAL — record names never reach wasm bytes (the oracle keeps records bare-keyed).
const MONO6_CORPUS: &[(&str, &str)] = &[
    (
        "r6_box_read",
        "module tool;\nrecord Box<T> { v: T }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; return 0 - b.v; }\n",
    ),
    (
        "r6_field_write",
        "module tool;\nrecord Box<T> { v: T }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut b: Box<i64> = Box { v: 1 }; b.v = 41; return 0 - b.v; }\n",
    ),
    (
        "r6_mixed_i64",
        "module tool;\nrecord P<T> { a: T, b: bool }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let p: P<i64> = P { a: 41, b: true }; return 0 - p.a; }\n",
    ),
    (
        "r6_mixed_bool",
        "module tool;\nrecord P<T> { a: T, b: bool }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let p: P<bool> = P { a: true, b: false }; return 7; }\n",
    ),
    (
        "r6_two_inst",
        "module tool;\nrecord Box<T> { v: T }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: Box<i64> = Box { v: 41 }; let c: Box<bool> = Box { v: true }; return 0 - a.v; }\n",
    ),
    (
        "r6_two_tp",
        "module tool;\nrecord Pair<A, B> { x: A, y: B }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let p: Pair<i64, bool> = Pair { x: 41, y: true }; return 0 - p.x; }\n",
    ),
    (
        "r6_plainrec_targ",
        "module tool;\nrecord Foo { n: i64 }\nrecord Box<T> { v: T }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let f: Foo = Foo { n: 41 }; let b: Box<Foo> = Box { v: f }; let g: Foo = b.v; return 0 - g.n; }\n",
    ),
    (
        "r6_construct_arg",
        "module tool;\nrecord Box<T> { v: T }\nfn get(b: Box<i64>) -> i64 { return b.v; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: Box<i64> = Box { v: 41 }; return 0 - get(a); }\n",
    ),
    // Folded sweep permanents (2026-07-13): a generic record as a MONO fn's param (no let) and a
    // 3-use dedup (3 refs -> exactly 1 cloned def).
    (
        "r6_param_only",
        "module tool;
record Box<T> { v: T }
fn rd(b: Box<i64>) -> i64 { return b.v; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; return 0 - rd(b); }
",
    ),
    (
        "r6_triple_dedup",
        "module tool;
record Box<T> { v: T }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: Box<i64> = Box { v: 10 }; let b: Box<i64> = Box { v: 11 }; let c: Box<i64> = Box { v: 20 }; return 0 - (a.v + b.v + c.v); }
",
    ),
    (
        "r6_nested_field",
        "module tool;\nrecord Box<T> { v: T }\nrecord Wrap<T> { inner: Box<T> }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let w: Wrap<i64> = Wrap { inner: Box { v: 41 } }; let b: Box<i64> = w.inner; return 0 - b.v; }\n",
    ),
];

/// MONO-6: whole-module byte identity over the generic-record corpus — the expanded tree
/// (concrete defs cloned + annotations rewritten) emits the SAME bytes as the oracle compiling
/// the generic source (the oracle derives per-instantiation layouts at AIR time; the shadow
/// makes them concrete in the tree).
#[test]
fn mono6_whole_module_parity() {
    assert_module_parity("MONO-6", MONO6_CORPUS);
}

/// MONO-6 execution capstone: a generic-record program monomorphized BY mn_expand runs to the
/// same value as the oracle-compiled module (field read through the cloned concrete layout).
#[test]
fn mono6_execution_capstone() {
    let generic = MONO6_CORPUS[0].1; // r6_box_read: 0 - Box{v:41}.v = -41
    assert_execution_magnitude("MONO-6", "cap6", generic, 41);
}

/// MONO-6 determinism.
#[test]
fn mono6_deterministic() {
    assert_corpus_deterministic("MONO-6", MONO6_CORPUS);
}

/// MONO-6 fence (X-E8, one-sided LOUD): a FREE generic fn whose type-param is bound only THROUGH
/// a generic-record param (`get<T>(b: Box<T>)`, needing Box<T> ~ Box<i64> unification) is out of
/// scope — the resolver binds a tparam from a BARE-T param, not through a generic-record param
/// (that's the method-receiver path, MONO-7, which reads the receiver's known targs instead).
/// The oracle accepts + monomorphizes it; the shadow leaves `get` generic -> the W-lane poisons
/// LOUD (a missing instance the differential names, never a wrong byte).
#[test]
fn mono6_fence_generic_fn_generic_record_param() {
    let src = "module tool;\nrecord Box<T> { v: T }\nfn get<T>(b: Box<T>) -> T { return b.v; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: Box<i64> = Box { v: 41 }; return 0 - get(a); }\n";
    let oracle = oracle_wasm_hex("f6_gfn", src);
    let shadow = mnexp_hex(src);
    assert!(
        !oracle.is_empty(),
        "MONO-6 fence: the oracle accepts the generic-fn-generic-record-param program"
    );
    assert!(
        shadow.contains("!!"),
        "MONO-6 fence: the shadow must poison LOUD (not silently emit wrong bytes): shadow_len={}",
        shadow.len()
    );
    assert_ne!(
        oracle, shadow,
        "MONO-6 fence: the shadow must NOT claim byte-identity on the fenced shape"
    );
}

/// MONO-6 fence (X-E8, LOUD): two MONO-5×MONO-6 interaction shapes need a fixpoint (records
/// concrete BEFORE fn typing) or targs threaded through a field access — both out of scope.
/// An inline chained read through a nested generic field (`w.inner.v`) resolves `w.inner` to the
/// BASE record code, losing `<i64>` (the pre-existing AG-G19 tc limit — targs are NOT threaded
/// through a SECOND field hop), so `.v` is out-of-core -> the W-lane poisons LOUD (a missing
/// read the differential names, never a wrong byte). The workaround (r6_nested_field) binds
/// `w.inner` to an annotated local. NOTE: the sibling `id(b.v)` shape (generic-fn arg = a ONE-hop
/// generic-record field read) is NO LONGER fenced — MONO-7's targs-on-let binding lets `b.v` type
/// as i64, so `id` resolves; it moved to MONO7_CORPUS (m7_fn_arg_fieldread) as an accept.
#[test]
fn mono6_fence_mono5_interaction() {
    let src = "module tool;\nrecord Box<T> { v: T }\nrecord Wrap<T> { inner: Box<T> }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let w: Wrap<i64> = Wrap { inner: Box { v: 41 } }; return 0 - w.inner.v; }\n";
    let oracle = oracle_wasm_hex("f6_chain_read", src);
    let shadow = mnexp_hex(src);
    assert!(!oracle.is_empty(), "MONO-6 fence: oracle accepts");
    assert!(
        shadow.contains("!!"),
        "MONO-6 fence: the shadow must poison LOUD on a chained nested read (len={})",
        shadow.len()
    );
    assert_ne!(oracle, shadow, "MONO-6 fence: no false byte-identity");
}

// ── MONO-7: generic-impl-method expansion — clone method instances to top-level fns ─────────
//
// mn_expand's P_K_METHOD arm resolves `b.get()` (receiver record + targs from binds), clones the
// method to a top-level concrete fn `Box__get__i64` (flag 2^21 -> cv exports it module-qualified
// `tool::Box__get__i64`, matching the oracle), and defers a call-site text patch + sets the
// pre-resolved flag so ST-2 resolves via n.text (not the `Box__i64__get` order the plain mangle
// would give). Runs BEFORE MONO-6's record rewrite (receiver targs read from the intact `Box<i64>`).
const MONO7_CORPUS: &[(&str, &str)] = &[
    (
        "m7_field",
        "module tool;\nrecord Box<T> { v: T }\nimpl Box<T> { pub fn get(self: Box<T>) -> T { return self.v; } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; return 0 - b.get(); }\n",
    ),
    (
        "m7_arg",
        "module tool;\nrecord Box<T> { v: T }\nimpl Box<T> { pub fn add(self: Box<T>, k: i64) -> i64 { return self.v + k; } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 40 }; return 0 - b.add(1); }\n",
    ),
    (
        "m7_two_inst",
        "module tool;\nrecord Box<T> { v: T }\nimpl Box<T> { pub fn id(self: Box<T>) -> T { return self.v; } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: Box<i64> = Box { v: 41 }; let c: Box<bool> = Box { v: true }; let d: bool = c.id(); return 0 - a.id(); }\n",
    ),
    (
        "m7_let",
        "module tool;\nrecord Box<T> { v: T }\nimpl Box<T> { pub fn get(self: Box<T>) -> T { return self.v; } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; let r: i64 = b.get(); return 0 - r; }\n",
    ),
    (
        "m7_calls_free",
        "module tool;\nrecord Box<T> { v: T }\nfn dbl<T>(x: T) -> T { return x; }\nimpl Box<T> { pub fn get(self: Box<T>) -> T { return dbl(self.v); } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; return 0 - b.get(); }\n",
    ),
    (
        "m7_calls_method",
        "module tool;\nrecord Box<T> { v: T }\nimpl Box<T> { pub fn inner(self: Box<T>) -> T { return self.v; } pub fn outer(self: Box<T>) -> T { return self.inner(); } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; return 0 - b.outer(); }\n",
    ),
    // MONO-7 side effect (was a MONO-6 interaction fence): the targs-on-let binding lets a ONE-hop
    // generic-record field read `b.v` type as i64, so a generic fn taking it (`id(b.v)`) resolves.
    (
        "m7_fn_arg_fieldread",
        "module tool;\nrecord Box<T> { v: T }\nfn id<T>(x: T) -> T { return x; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; let n: i64 = id(b.v); return 0 - n; }\n",
    ),
];

/// MONO-7: whole-module byte identity over the generic-method corpus (the module-qualified
/// `tool::Box__get__i64` export + the desugared call all match the oracle).
#[test]
fn mono7_whole_module_parity() {
    assert_module_parity("MONO-7", MONO7_CORPUS);
}

/// MONO-7 execution capstone: a generic-method program monomorphized BY mn_expand runs to the
/// same value as the oracle (the method instance called through its FuncId).
#[test]
fn mono7_execution_capstone() {
    let generic = MONO7_CORPUS[0].1; // m7_field: 0 - Box{v:41}.get() = -41
    assert_execution_magnitude("MONO-7", "cap7", generic, 41);
}

/// MONO-7 determinism.
#[test]
fn mono7_deterministic() {
    assert_corpus_deterministic("MONO-7", MONO7_CORPUS);
}

/// MONO-7 fence (X-E8 / AG-E4, one-sided LOUD): a method with its OWN type-param (`fn map<U>`)
/// can't be monomorphized from the receiver's targs (U comes from the arg) — cloning would
/// half-substitute (T->i64, U stays U) and emit SILENT wrong bytes. The guard leaves the call
/// generic so ST-2's `Box__i64__map` misses -> the W-lane poisons LOUD (never wrong bytes).
#[test]
fn mono7_fence_method_own_type_param() {
    let src = "module tool;\nrecord Box<T> { v: T }\nimpl Box<T> { pub fn map<U>(self: Box<T>, u: U) -> T { return self.v; } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; return 0 - b.map(true); }\n";
    let oracle = oracle_wasm_hex("f7_own_tp", src);
    let shadow = mnexp_hex(src);
    assert!(!oracle.is_empty(), "MONO-7 fence: oracle accepts");
    assert!(
        shadow.contains("!!"),
        "MONO-7 fence: the shadow must poison LOUD on a method-own-tp, not emit wrong bytes (len={})",
        shadow.len()
    );
    assert_ne!(oracle, shadow, "MONO-7 fence: no false byte-identity");
}

// ── B-VEC: the vec_load/vec_store/alloc intrinsics in the W-lane
//
// Every stdlib Vec method body calls the memory intrinsics; the W-lane now lowers them
// byte-identically to the oracle (air.rs:2458-2556): alloc -> CVS_IALLOC (i32-operand, call 4,
// i64.extend_i32_u); vec_load/vec_store -> the bound trap (wrap idx, wrap bound, GtEq, TrapIf)
// + WrapI64 base->Ptr + LD0/SD0 (elem_size 8, memarg offset 0 — header-less, vs the array kinds'
// offset 4). The byte arbiter is oracle_wasm_hex (the DIRECT pipeline — compile_tool would
// ambient-inject option/result as extra modules with their own __init fns, out of the W-lane's
// single-module world).
fn bvec_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    vec![
        (
            "bv_alloc",
            "module tool;\nfn mk(n: i64) -> i64 !{ Alloc } { return alloc(n); }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { let b: i64 = mk(32); return 0 - 41; }\n".to_string(),
        ),
        (
            "bv_get",
            format!("module tool;\n{vecsrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let v: Vec<i64> = Vec {{ buf: 0, count: 0, slots: 1, alloc: 0 }}; let x: i64 = v.get(0); return 0 - 41; }}\n"),
        ),
        (
            "bv_set",
            format!("module tool;\n{vecsrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<i64> = Vec {{ buf: 0, count: 1, slots: 1, alloc: 0 }}; let q: i64 = v.set(0, 41); return 0 - 41; }}\n"),
        ),
        (
            "bv_set_get_roundtrip",
            format!("module tool;\n{vecsrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<i64> = Vec {{ buf: 0, count: 1, slots: 1, alloc: 0 }}; let q: i64 = v.set(0, 41); let x: i64 = v.get(0); return 0 - x; }}\n"),
        ),
    ]
}

/// B-VEC: whole-module byte identity — monomorphized Vec.get/Vec.set (whose bodies are the
/// vec_load/vec_store intrinsics) + a user alloc fn, all byte-identical to the oracle.
#[test]
fn bvec_whole_module_parity() {
    assert_module_parity("B-VEC", &bvec_corpus());
}

/// B-VEC execution capstone: the set->get roundtrip through the monomorphized Vec methods RUNS
/// to -41 (the store landed, the load found it, the bound traps stayed quiet).
#[test]
fn bvec_execution_capstone() {
    let corpus = bvec_corpus();
    let source = corpus_source(&corpus, "bv_set_get_roundtrip");
    assert_execution_magnitude("B-VEC", "bvcap", source, 41);
}

/// B-VEC determinism.
#[test]
fn bvec_deterministic() {
    assert_corpus_deterministic("B-VEC", &bvec_corpus());
}

// ── B-LET: unannotated lets in the W-lane (the B-VEC push fence FLIPPED to an accept) ────────
//
// B-LET admits `let e = <value>;` (no annotation): the subset gate takes an in-subset,
// non-aggregate value; the CV emit types the local from the VALUE (cv_expr_tytok,
// intrinsic-aware) and POISONS loud on "?". A record-valued unannotated let binds rec=-1 —
// a field use through it poisons at the USE site (fail-closed). This closed the LAST blocker
// for Vec.push (its grow loop's `let e = vec_load(..)`); the B-LET Phase-0 measured that
// param-field writes, field==field conds, and compound field increments were ALREADY green.
const BLET_CORPUS: &[(&str, &str)] = &[
    (
        "bl_unannot_int",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let e = 5; return 0 - e; }\n",
    ),
    (
        "bl_unannot_call",
        "module tool;\nfn g(x: i64) -> i64 { return x + 1; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let e = g(40); return 0 - e; }\n",
    ),
    (
        "bl_unannot_binary",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a = 40; let b = a + 1; return 0 - b; }\n",
    ),
    (
        "bl_unannot_field",
        "module tool;\nrecord Bx { v: i64 }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Bx = Bx { v: 41 }; let e = b.v; return 0 - e; }\n",
    ),
    (
        "bl_unannot_in_while",
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < 3 { let d = i * 2; s = s + d; i = i + 1; } return 0 - (s + 35); }\n",
    ),
    (
        "bl_param_field_write",
        "module tool;\nrecord Bx { v: i64 }\nfn setv(b: Bx @Mut, k: i64) -> i64 { b.v = k; return b.v; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut b: Bx = Bx { v: 1 }; let r: i64 = setv(b, 41); return 0 - r; }\n",
    ),
];

/// B-LET: whole-module byte identity over the unannotated-let corpus.
#[test]
fn blet_whole_module_parity() {
    assert_module_parity("B-LET", BLET_CORPUS);
}

/// THE RATCHET FLIP (was bvec_fence_push_unannotated_let): Vec.push — construct, push through
/// the GROW loop (alloc + the doubling vec_load/vec_store copy + param-field writes +
/// `let e = vec_load(..)`), then get — is whole-module BYTE-IDENTICAL and RUNS to -41. The
/// full leaf Vec surface (get/set/push) is live in the W-lane.
#[test]
fn blet_push_roundtrip_accept() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let src = format!(
        "module tool;\n{vecsrc}\nfn mk() -> Vec<i64> {{ let v: Vec<i64> = Vec {{ buf: 0, count: 0, slots: 0, alloc: 0 }}; return v; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<i64> = mk(); let q: i64 = v.push(41); let x: i64 = v.get(0); return 0 - x; }}\n"
    );
    assert_execution_magnitude("B-LET push", "bl_push", &src, 41);
}

/// B-LET fence (one-sided LOUD): a RECORD-valued unannotated let (`let b = mk(); b.v`) binds
/// rec=-1 — the field USE poisons loud (the designed fail-closed posture, never wrong bytes).
/// (The Arena shape FLIPPED to a B-DISPATCH accept — see bdisp_arena_roundtrip_accept.)
#[test]
fn blet_fences() {
    let shapes: Vec<(&str, String)> = vec![
        ("bl_fence_rec_unannot", "module tool;\nrecord Bx { v: i64 }\nfn mk() -> Bx { return Bx { v: 41 }; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b = mk(); return 0 - b.v; }\n".to_string()),
    ];
    for (label, src) in &shapes {
        let oracle = oracle_wasm_hex(label, src);
        let shadow = mnexp_hex(src);
        assert!(!oracle.is_empty(), "B-LET fence {label}: oracle accepts");
        assert!(
            shadow.contains("!!"),
            "B-LET fence {label}: the shadow must poison LOUD (len={})",
            shadow.len()
        );
        assert_ne!(
            oracle, shadow,
            "B-LET fence {label}: no false byte-identity"
        );
    }
}

// ── B-DISPATCH: field/chain-receiver method dispatch (Arena/Map delegation goes live) ────────
//
// The crux BOOT-SELF capability, in two layers: (air) ST-2's receiver may be ONE field hop —
// cv_recv_rec resolves the record through the base's env rec + the field's ftag, and the
// receiver materializes via cv_to_var (the LoadField temp) AFTER the call dst freshes (X6);
// (mn) the P_K_METHOD arm derives a FIELD receiver's targs through the GENERIC def's field type
// (`store: Vec<T>` + the base's targs -> Vec<i64>) via mn_field_targs, then the MONO-7
// clone/patch machinery. Enum-ctor paths fail-safe (no bind named `E` -> targs "").
#[test]
fn bdisp_whole_module_parity() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let arenasrc = strip_module(include_str!("../../../stdlib/sigil/arena.sigil"), "arena");
    let cases: &[(&str, String)] = &[
        ("bd_concrete", "module tool;\nrecord In { v: i64 }\nimpl In { pub fn getv(self: In) -> i64 { return self.v; } }\nrecord Out { inner: In }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let o: Out = Out { inner: In { v: 41 } }; return 0 - o.inner.getv(); }\n".to_string()),
        ("bd_concrete_arg", "module tool;\nrecord In { v: i64 }\nimpl In { pub fn addv(self: In, k: i64) -> i64 { return self.v + k; } }\nrecord Out { inner: In }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let o: Out = Out { inner: In { v: 40 } }; return 0 - o.inner.addv(1); }\n".to_string()),
        ("bd_arena", format!("module tool;\n{vecsrc}\n{arenasrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<i64> = Arena {{ store: Vec {{ buf:0, count:0, slots:0, alloc:0 }} }}; let id: i64 = a.allocate(41); let x: i64 = a.get(id); return 0 - x; }}")),
        ("bd_arena_set", format!("module tool;\n{vecsrc}\n{arenasrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<i64> = Arena {{ store: Vec {{ buf:0, count:0, slots:0, alloc:0 }} }}; let id: i64 = a.allocate(1); let q: i64 = a.set(id, 41); let x: i64 = a.get(id); return 0 - x; }}")),
    ];
    assert_module_parity("B-DISPATCH", cases);
}

/// THE RATCHET FLIP (was bl_fence_arena): the Arena allocate->get roundtrip — construct, allocate
/// (delegating self.store.push through the field receiver), get (delegating self.store.get) —
/// is whole-module BYTE-IDENTICAL and RUNS to -41. Arena delegation is live.
#[test]
fn bdisp_arena_roundtrip_accept() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let arenasrc = strip_module(include_str!("../../../stdlib/sigil/arena.sigil"), "arena");
    let src = format!(
        "module tool;\n{vecsrc}\n{arenasrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<i64> = Arena {{ store: Vec {{ buf:0, count:0, slots:0, alloc:0 }} }}; let id: i64 = a.allocate(41); let x: i64 = a.get(id); return 0 - x; }}"
    );
    assert_execution_magnitude("B-DISPATCH arena", "bd_arena_run", &src, 41);
}

/// B-DISPATCH determinism.
#[test]
fn bdisp_deterministic() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let arenasrc = strip_module(include_str!("../../../stdlib/sigil/arena.sigil"), "arena");
    let src = format!(
        "module tool;\n{vecsrc}\n{arenasrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<i64> = Arena {{ store: Vec {{ buf:0, count:0, slots:0, alloc:0 }} }}; let id: i64 = a.allocate(41); let x: i64 = a.get(id); return 0 - x; }}"
    );
    assert_corpus_deterministic("B-DISPATCH", &[("bd_arena", src)]);
}

// ── B-ASSOC: associated-fn expansion (`Vec::new()` / `Arena::new()` — the stdlib idiom) ───────
//
// `Type::assoc(args)` parses as P_K_METHOD { text: meth, child0: P_K_PATH(Type), args… } (the
// parser's leading-segments-receiver quirk). The mn layer resolves it from CONTEXT — (a) a
// let-annotation whose record names the receiver type (`let v: Vec<i64> = Vec::new()`), or (b) a
// construct FIELD whose generic-def field type maps through the enclosing clone's subst
// (`Arena { store: Vec::new() }` inside Arena::new's T→i64 clone) — then REWRITES the node in
// place to a plain P_K_CALL of the instance mangle (receiver path dropped: an associated fn has
// no self arg). The clone rides the MONO-7 method-instance machinery (2^21 export flag).
#[test]
fn bassoc_whole_module_parity() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let arenasrc = strip_module(include_str!("../../../stdlib/sigil/arena.sigil"), "arena");
    let cases: &[(&str, String)] = &[
        (
            "ba_vec_new",
            format!(
                "module tool;\n{vecsrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<i64> = Vec::new(); let q: i64 = v.push(41); let x: i64 = v.get(0); return 0 - x; }}\n"
            ),
        ),
        (
            "ba_vec_new_dedup",
            format!(
                "module tool;\n{vecsrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<i64> = Vec::new(); let mut w: Vec<i64> = Vec::new(); let q1: i64 = v.push(40); let q2: i64 = w.push(1); let a: i64 = v.get(0); let b: i64 = w.get(0); return 0 - a - b; }}\n"
            ),
        ),
        (
            "ba_arena_new",
            format!(
                "module tool;\n{vecsrc}\n{arenasrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<i64> = Arena::new(); let id: i64 = a.allocate(41); let x: i64 = a.get(id); return 0 - x; }}\n"
            ),
        ),
    ];
    assert_module_parity("B-ASSOC", cases);
}

/// THE CAPSTONE: the pure-stdlib idiom — `Vec::new()` + push + get with NO literal construct
/// anywhere (the exact line every selfhost module writes) — byte-identical and RUNS to -41.
#[test]
fn bassoc_vec_lifecycle_accept() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let src = format!(
        "module tool;\n{vecsrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<i64> = Vec::new(); let q: i64 = v.push(41); let x: i64 = v.get(0); return 0 - x; }}\n"
    );
    assert_execution_magnitude("B-ASSOC vec lifecycle", "ba_vec_run", &src, 41);
}

/// `Arena::new()` end-to-end: the assoc clone's BODY construct field (`store: Vec::new()`)
/// resolves through the enclosing clone's subst (T -> i64) — the construct-field context —
/// producing the oracle's post-order (Vec__new__i64 FIRST), then the B-DISPATCH delegation
/// chain. Byte-identical and RUNS to -41.
#[test]
fn bassoc_arena_lifecycle_accept() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let arenasrc = strip_module(include_str!("../../../stdlib/sigil/arena.sigil"), "arena");
    let src = format!(
        "module tool;\n{vecsrc}\n{arenasrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<i64> = Arena::new(); let id: i64 = a.allocate(41); let x: i64 = a.get(id); return 0 - x; }}\n"
    );
    assert_execution_magnitude("B-ASSOC arena lifecycle", "ba_arena_run", &src, 41);
}

/// B-ASSOC fence (one-sided LOUD): an assoc call in ARG position (`consume(Vec::new())`) has no
/// covered context (the oracle infers from the param type; the shadow's contexts are
/// let-annotation + construct-field only) — the call stays generic and the W-lane poisons.
/// Never wrong bytes. (`let v = Vec::new()` unannotated is NOT a fence: the oracle itself
/// rejects it, T150 — reject-parity, no exposure.)
#[test]
fn bassoc_fences() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let shapes: Vec<(&str, String)> = vec![(
        "ba_fence_argpos",
        format!(
            "module tool;\n{vecsrc}\nfn consume(v: Vec<i64>) -> i64 {{ return v.count; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return consume(Vec::new()); }}\n"
        ),
    )];
    for (label, src) in &shapes {
        let oracle = oracle_wasm_hex(label, src);
        let shadow = mnexp_hex(src);
        assert!(!oracle.is_empty(), "B-ASSOC fence {label}: oracle accepts");
        assert!(
            shadow.contains("!!"),
            "B-ASSOC fence {label}: the shadow must poison LOUD (len={})",
            shadow.len()
        );
        assert_ne!(
            oracle, shadow,
            "B-ASSOC fence {label}: no false byte-identity"
        );
    }
}

/// B-ASSOC determinism.
#[test]
fn bassoc_deterministic() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let arenasrc = strip_module(include_str!("../../../stdlib/sigil/arena.sigil"), "arena");
    let src = format!(
        "module tool;\n{vecsrc}\n{arenasrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<i64> = Arena::new(); let id: i64 = a.allocate(41); let x: i64 = a.get(id); return 0 - x; }}\n"
    );
    assert_corpus_deterministic("B-ASSOC", &[("ba_arena", src)]);
}

// ── W-STR-A: str intrinsic methods (len / byte_at / substr) in the W-lane ────────────────────
//
// The first CAP-0 ratchet slice. str = (ptr U32 @0, len U32 @4); the `$str` elem sentinel
// (stamped at param/let seeding) discriminates str receivers from records/arrays (all token
// "Ptr" by the render contract). len = LF2-U32(4) + ExtendU32(173); byte_at = the trap chain +
// Load8(45) + the width-8 extend; substr = 4 arg traps + two CONSTANT-TIME UTF-8 boundary
// checks (CtSelect lowers BRANCHLESSLY: else ^ ((then ^ else) & (0 - extend(cond))) — never
// wasm select) + BA(8,4) + two U32 stores. Bool operands ride the i32 op class (i32.and 113 /
// i32.eq 70). The per-alloc FuelDecrement comes from the shared fuel machinery, not the emitter.
const WSTRA_CORPUS: &[(&str, &str)] = &[
    (
        "ws_len",
        "module tool;
fn f(s: str) -> i64 { return s.len(); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let s: str = \"abcd\"; let n: i64 = f(s); return 0 - (n + 37); }
",
    ),
    (
        "ws_byte_at",
        "module tool;
fn g(s: str, i: i64) -> i64 { return s.byte_at(i); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let s: str = \"A\"; let b: i64 = g(s, 0); return 0 - (b - 24); }
",
    ),
    (
        "ws_substr",
        "module tool;
fn h(s: str, a: i64, b: i64) -> str { return s.substr(a, b); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let s: str = \"hello\"; let t: str = h(s, 1, 3); let n: i64 = t.len(); return 0 - (n + 39); }
",
    ),
    (
        "ws_combined",
        "module tool;
fn u(s: str) -> i64 { let t: str = s.substr(1, 4); let n: i64 = t.len(); let b: i64 = t.byte_at(0); return n + b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let s: str = \"xabcy\"; let r: i64 = u(s); return 0 - (r - 59); }
",
    ),
];

#[test]
fn wstra_whole_module_parity() {
    assert_module_parity("W-STR-A", WSTRA_CORPUS);
}

/// Execution: the substr+len+byte_at chain runs to -41 through the shadow-emitted module.
#[test]
fn wstra_execution_accept() {
    let source = corpus_source(WSTRA_CORPUS, "ws_combined");
    assert_execution_magnitude("W-STR-A", "ws_run", source, 41);
}

/// W-STR-A fences (one-sided LOUD, W-STR-FIELD flip): a ONE-hop field str receiver now emits
/// (see wsf2 corpus) — the fence moves to a TWO-hop chain (`o.inner.s.len()`), which stays
/// outside the surface and poisons; never wrong bytes.
#[test]
fn wstra_fences() {
    let shapes: &[(&str, &str)] = &[(
        "ws_fence_two_hop",
        "module tool;
record R { s: str }
record O { inner: R }
fn f(o: O) -> i64 { return o.inner.s.len(); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let r: R = R { s: \"ab\" }; let o: O = O { inner: r }; return 0 - f(o); }
",
    )];
    for (label, src) in shapes {
        let oracle = oracle_wasm_hex(label, src);
        let shadow = mnexp_hex(src);
        assert!(!oracle.is_empty(), "W-STR fence {label}: oracle accepts");
        assert!(
            shadow.contains("!!"),
            "W-STR fence {label}: the shadow must poison LOUD (len={})",
            shadow.len()
        );
    }
}

/// Determinism.
#[test]
fn wstra_deterministic() {
    let source = corpus_source(WSTRA_CORPUS, "ws_substr");
    assert_corpus_deterministic("W-STR-A", &[("ws_substr", source)]);
}

// ── W-STR-B: the str-method DESUGAR + store8 + cross-module calls in the W-lane ──────────────
//
// The five stdlib-backed methods (.concat/.bytes_eq/.join/.contains on $str receivers; .itoa on
// I64) lower to a PLAIN Call of the module-qualified stdlib fn with the receiver as arg0 (the
// oracle's tc desugar; FuncId = the cross-module decl-order basis, bare-name lookup — str_*
// names are unique across modules). store8(ptr, byte) = IntrinsicStore8: the VALUE stays i64
// (i64.store8 = 60; only i32-width values take i32.store8 = 58); the expr-stmt phantom Unit dst
// mirrors the oracle's skipped local. Covered shapes proven byte-identical include cond-position
// bytes_eq and let-chained substr->concat receivers. The census named the NEXT class: top-level
// CONST references (wb_ident_slice is const-free and green; the const form = W-CONST).
#[test]
fn wstrb_whole_module_parity() {
    let cases: &[(&str, &str)] = &[
        (
            "wb_concat",
            "module tool;\nfn f(a: str, b: str) -> str { return a.concat(b); }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: str = \"ab\"; let y: str = \"cd\"; let z: str = f(x, y); return 0 - (z.len() + 37); }\nmodule string;\npub fn str_concat(x: str, y: str) -> str ! { Alloc } { return x; }\n",
        ),
        (
            "wb_itoa",
            "module tool;\nfn g(v: i64) -> str { return v.itoa(); }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let s: str = g(7); return 0 - (s.len() + 40); }\nmodule string;\npub fn str_itoa(v: i64) -> str ! { Alloc } { return \"x\"; }\n",
        ),
        (
            "wb_bytes_eq",
            "module tool;\nfn h(a: str, b: str) -> bool { return a.bytes_eq(b); }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: str = \"ab\"; let y: str = \"ab\"; let e: bool = h(x, y); if e { return 0 - 41; } else { } return 0 - 7; }\nmodule strings;\npub fn str_bytes_eq(x: str, y: str) -> bool { return true; }\n",
        ),
        (
            "wb_store8",
            r#"module string;
pub fn w8(p: i64, b: i64) -> i64 ! { Alloc } { store8(p, b); return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { let buf: i64 = alloc(1); let q: i64 = w8(buf, 65); return 0 - 41; }
"#,
        ),
        (
            "wb_cond",
            r#"module tool;
fn t(s: str) -> i64 { if s.bytes_eq("fn") { return 1; } else { } return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: str = "fn"; return 0 - (t(x) + 40); }
module strings;
pub fn str_bytes_eq(x: str, y: str) -> bool { return true; }
"#,
        ),
        (
            "wb_unannot",
            r#"module tool;
fn u(s: str) -> i64 { let t: str = s.substr(0, 2); let w: str = t.concat(t); return w.len(); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: str = "abcd"; return 0 - (u(x) + 37); }
module string;
pub fn str_concat(x: str, y: str) -> str ! { Alloc } { return x; }
"#,
        ),
        (
            "wb_ident_slice",
            r#"module tool;
fn ident_tag(lex: str) -> i64 {
    let n: i64 = lex.len();
    if n == 2 {
        if lex.bytes_eq("fn") {
            return 70;
        } else {
        }
        if lex.bytes_eq("if") {
            return 71;
        } else {
        }
    } else {
    }
    return 5;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: str = "fn"; return 0 - (ident_tag(x) - 29); }
module strings;
pub fn str_bytes_eq(x: str, y: str) -> bool { return true; }
"#,
        ),
    ];
    assert_module_parity("W-STR-B", cases);
}

/// Execution: the desugared bytes_eq drives control flow to -41 through the shadow module.
#[test]
fn wstrb_execution_accept() {
    let src = r#"module tool;
fn t(s: str) -> i64 { if s.bytes_eq("fn") { return 1; } else { } return 0; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: str = "fn"; return 0 - (t(x) + 40); }
module strings;
pub fn str_bytes_eq(x: str, y: str) -> bool {
    let n: i64 = x.len();
    let m: i64 = y.len();
    if n == m {
    } else {
        return false;
    }
    let mut i: i64 = 0;
    while i < n {
        if x.byte_at(i) == y.byte_at(i) {
        } else {
            return false;
        }
        i = i + 1;
    }
    return true;
}
"#;
    assert_execution_magnitude("W-STR-B", "wb_run", src, 41);
}

/// Determinism.
#[test]
fn wstrb_deterministic() {
    let src = r#"module tool;
fn f(a: str, b: str) -> str { return a.concat(b); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: str = "ab"; let y: str = "cd"; let z: str = f(x, y); return 0 - (z.len() + 37); }
module string;
pub fn str_concat(x: str, y: str) -> str ! { Alloc } { return x; }
"#;
    assert_corpus_deterministic("W-STR-B", &[("wb_concat", src)]);
}

// ── W-CONST: top-level const references INLINED in the W-lane ────────────────────────────────
//
// The oracle fully inlines every const reference as a fresh IntLit temp (reference order =
// fresh order; no globals, no memory). The shadow builds a const table from all modules'
// P_K_CONST nodes (text = `name;literal`, INT littype only — a non-int const's reference
// misses the table and poisons LOUD) threaded through the cv family; cv_to_var's bare-path
// arm inlines on env+variant miss, and cv_expr_tytok types a const ref I64 (the operand/
// binop-dst widths depend on it — the wc_arith convergence found that).
#[test]
fn wconst_whole_module_parity() {
    let cases: &[(&str, &str)] = &[
        (
            "wc_ref",
            "module tool;
const K: i64 = 70;
fn f() -> i64 { return K; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - (f() - 29); }
",
        ),
        (
            "wc_arith",
            "module tool;
const A: i64 = 7;
const B: i64 = 5;
fn g(x: i64) -> i64 { if x == A { return B; } else { } return A + B; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - (g(7) + 36); }
",
        ),
        (
            "wc_ident_full",
            r#"module tool;
const T_KW_FN: i64 = 70;
const T_KW_IF: i64 = 71;
const T_IDENT: i64 = 5;
fn ident_tag(lex: str) -> i64 {
    let n: i64 = lex.len();
    if n == 2 {
        if lex.bytes_eq("fn") {
            return T_KW_FN;
        } else {
        }
        if lex.bytes_eq("if") {
            return T_KW_IF;
        } else {
        }
    } else {
    }
    return T_IDENT;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let x: str = "fn"; return 0 - (ident_tag(x) - 29); }
module strings;
pub fn str_bytes_eq(x: str, y: str) -> bool { return true; }
"#,
        ),
    ];
    assert_module_parity("W-CONST", cases);
}

/// Execution: the const-driven return runs to -41 through the shadow module.
#[test]
fn wconst_execution_accept() {
    let src = "module tool;
const K: i64 = 70;
fn f() -> i64 { return K; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - (f() - 29); }
";
    assert_execution_magnitude("W-CONST", "wc_run", src, 41);
}

/// Determinism.
#[test]
fn wconst_deterministic() {
    let src = "module tool;
const A: i64 = 7;
const B: i64 = 5;
fn g(x: i64) -> i64 { if x == A { return B; } else { } return A + B; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - (g(7) + 36); }
";
    assert_corpus_deterministic("W-CONST", &[("wc_arith", src)]);
}

// ── W-TUPLE: tuple construct / destructure in the W-lane (the parser-block unlock) ─────────────
//
// The 339 W-CONST survivors bisect to TUPLES — ~45 parser fns return (id, pos) pairs. A tuple is
// a width-8 pair: construct = the reg4 record machinery at size 16 (BumpAlloc(16,8) + two I64
// StoreFields @0/@8); destructure = two I64 LoadFields. The ST-3 walker handled a tuple LOCAL
// RHS; W-TUPLE adds the CALL RHS (`let (x,y) = f(...)` — the parser's dominant shape): the
// callee sig's ret_detail ($tupleN__a$b) drives the element tokens, and cv_sig_ret_tok returns
// Ptr for a composite return (ret=Unit + ret_detail present) so the call dst is the pair pointer.
#[test]
fn wtuple_whole_module_parity() {
    let cases: &[(&str, &str)] = &[
        (
            "wt_tuple_ret",
            "module tool;
fn f(a: i64, b: i64) -> (i64, i64) { return (a, b + 1); }
fn h() -> i64 { let (x, y) = f(3, 4); return x + y; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - (h() + 33); }
",
        ),
        (
            "wt_tuple_construct_only",
            "module tool;
fn f(a: i64, b: i64) -> (i64, i64) { return (a, b + 1); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - 41; }
",
        ),
        (
            "wt_tuple_destructure_only",
            "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let p: (i64, i64) = (3, 4); let (x, y) = p; return 0 - (x + y + 34); }
",
        ),
    ];
    assert_module_parity("W-TUPLE", cases);
}

/// Execution: the (a, b+1) tuple return + destructure runs to -41.
#[test]
fn wtuple_execution_accept() {
    let src = "module tool;
fn f(a: i64, b: i64) -> (i64, i64) { return (a, b + 1); }
fn h() -> i64 { let (x, y) = f(3, 4); return x + y; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - (h() + 33); }
";
    assert_execution_magnitude("W-TUPLE", "wt_run", src, 41);
}

/// W-TUPLE fence (one-sided): a tuple-ANNOTATED let with a call RHS
// (`let p: (i64,i64) = f(...)`) is NOT the parser's shape (it writes `let (x,y) = f(...)`
// directly); the annotated-let-into-local tuple path stays unhandled and poisons/diverges.
#[test]
fn wtuple_deterministic() {
    let src = "module tool;
fn f(a: i64, b: i64) -> (i64, i64) { return (a, b + 1); }
fn h() -> i64 { let (x, y) = f(3, 4); return x + y; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - (h() + 33); }
";
    assert_corpus_deterministic("W-TUPLE", &[("wt_tuple_ret", src)]);
}

// ── W-ELEM: element-type-faithful Vec intrinsic emission ───────────────────────────────────
// The silent-divergence fix: record/str Vec elements are POINTERS (Ptr = u32) — the oracle
// accesses their slots with i32 ops + i32 locals (slot stride stays 8); the shadow's B-VEC arm
// hardcoded I64 and emitted same-length-but-different (and INVALID: i64 dst vs i32 result type)
// bytes with NO poison. The elem token now rides the Vec<T> WITNESS (vec_load) / the value's
// env binding (vec_store); the unknown/narrow classification POISONS loud (X-WE1/X-WE2).

fn welem_pre() -> String {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let arenasrc = strip_module(include_str!("../../../stdlib/sigil/arena.sigil"), "arena");
    format!("module tool;\n{vecsrc}\n{arenasrc}\nrecord PN {{ kind: i64, cs: i64, cc: i64 }}\n")
}

fn welem_corpus() -> Vec<(&'static str, String)> {
    let pre = welem_pre();
    vec![
        // record elements through Arena.get (the ubiquitous `nodes.get(x)` compiler shape).
        (
            "we_arena_get_rec",
            format!(
                "{pre}fn g(nodes: Arena<PN>, fnid: i64) -> i64 {{ let fnn: PN = nodes.get(fnid); return fnn.kind; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<PN> = Arena::new(); let q: i64 = a.allocate(PN {{ kind: 8, cs: 0, cc: 0 }}); return 0 - (g(a, 0) + 33); }}\n"
            ),
        ),
        // record elements through bare Vec.get.
        (
            "we_vec_get_rec",
            format!(
                "{pre}fn g(stmts: Vec<PN>, i: i64) -> i64 {{ let st: PN = stmts.get(i); return st.kind; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<PN> = Vec::new(); let q: i64 = v.push(PN {{ kind: 7, cs: 0, cc: 0 }}); return 0 - (g(v, 0) + 34); }}\n"
            ),
        ),
        // a record with a STR field (the real PNode/Token/CvStmt shape).
        (
            "we_strfield_rec",
            format!(
                "{pre}record PS {{ kind: i64, text: str }}\nfn g(nodes: Arena<PS>) -> i64 {{ let fnn: PS = nodes.get(0); return fnn.kind; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<PS> = Arena::new(); let q: i64 = a.allocate(PS {{ kind: 8, text: \"ab\" }}); return 0 - (g(a) + 33); }}\n"
            ),
        ),
        // str elements through bare Vec.get.
        (
            "we_vec_get_str",
            format!(
                "{pre}fn g(v: Vec<str>) -> i64 {{ let s: str = v.get(0); return s.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<str> = Vec::new(); let q: i64 = v.push(\"ab\"); return 0 - (g(v) + 39); }}\n"
            ),
        ),
        // record push x5 (forces the grow 4->8 copy loop: LD0+SD0 both elem-typed) + set + get.
        (
            "we_push_grow_rec",
            format!(
                "{pre}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<PN> = Vec::new(); let q1: i64 = v.push(PN {{ kind: 1, cs: 0, cc: 0 }}); let q2: i64 = v.push(PN {{ kind: 2, cs: 0, cc: 0 }}); let q3: i64 = v.push(PN {{ kind: 3, cs: 0, cc: 0 }}); let q4: i64 = v.push(PN {{ kind: 4, cs: 0, cc: 0 }}); let q5: i64 = v.push(PN {{ kind: 30, cs: 0, cc: 0 }}); let q6: i64 = v.set(0, PN {{ kind: 7, cs: 0, cc: 0 }}); let a: PN = v.get(0); let b: PN = v.get(4); let n: i64 = v.len(); return 0 - (a.kind + b.kind + n); }}\n"
            ),
        ),
        // str push x2 + get + len (Ptr-typed str slots end-to-end).
        (
            "we_push_get_str",
            format!(
                "{pre}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<str> = Vec::new(); let q1: i64 = v.push(\"ab\"); let q2: i64 = v.push(\"cdef\"); let s: str = v.get(1); let n: i64 = s.len(); let m: i64 = v.len(); return 0 - (n + m); }}\n"
            ),
        ),
        // the i64-element BASELINE (X-WE4: bytes must stay what B-VEC pinned).
        (
            "we_arena_get_i64",
            format!(
                "{pre}fn g(xs: Arena<i64>) -> i64 {{ let v: i64 = xs.get(0); return v; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<i64> = Arena::new(); let q: i64 = a.allocate(41); return 0 - g(a); }}\n"
            ),
        ),
        // the full ai_is_generic_fn body clone (integration: Arena<rec>.get + Vec<i64>.get + CF).
        (
            "we_isg_clone",
            format!(
                "{pre}fn g(nodes: Arena<PN>, kids: Vec<i64>, fnid: i64) -> bool {{ let fnn: PN = nodes.get(fnid); let mut i: i64 = 0; let mut found: bool = false; let mut scanning: bool = true; while scanning {{ if i >= fnn.cc {{ scanning = false; }} else {{ let cid: i64 = kids.get(fnn.cs + i); let cn: PN = nodes.get(cid); if cn.kind == 7 {{ found = true; scanning = false; }} else {{ i = i + 1; }} }} }} return found; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<PN> = Arena::new(); let q: i64 = a.allocate(PN {{ kind: 7, cs: 0, cc: 0 }}); let mut k: Vec<i64> = Vec::new(); let q2: i64 = k.push(0); let b: bool = g(a, k, 0); if b {{ return 0 - 44; }} else {{ return 0 - 45; }} }}\n"
            ),
        ),
    ]
}

/// W-ELEM: whole-module byte parity across the elem-type corpus (record/str elems flip from
/// silent divergence to identity; the i64 baseline stays pinned).
#[test]
fn welem_byte_parity() {
    assert_module_parity("W-ELEM", &welem_corpus());
}

/// W-ELEM execution capstone (record elems): pre-fix the shadow emitted an i64 local returned
/// against an i32 result type — an INVALID module; running the shadow bytes is the proof.
/// -(7 + 30 + 5) = -42.
#[test]
fn welem_exec_capstone_rec() {
    let corpus = welem_corpus();
    let source = corpus_source(&corpus, "we_push_grow_rec");
    assert_execution_magnitude("W-ELEM record", "we_exec_rec", source, 42);
}

/// W-ELEM execution capstone (str elems): -(4 + 2) = -6.
#[test]
fn welem_exec_capstone_str() {
    let corpus = welem_corpus();
    let source = corpus_source(&corpus, "we_push_get_str");
    assert_execution_magnitude("W-ELEM str", "we_exec_str", source, 6);
}

/// W-ELEM narrow-elem fence (AG-WE1, one-sided LOUD): Vec<bool> is oracle-valid but outside the
/// shadow's closed elem set {i64, str, record} — the shadow POISONS (upgraded from the pre-W-ELEM
/// silent wrong-width bytes), never emits a defaulted width.
#[test]
fn welem_narrow_fence() {
    let pre = welem_pre();
    let src = format!(
        "{pre}fn g(v: Vec<i32>) -> i64 {{ let b: i32 = v.get(0); return 41; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<i32> = Vec::new(); let n: i64 = 41; let x: i32 = n.as_i32(); let q: i64 = v.push(x); return 0 - g(v); }}\n"
    );
    let oracle = oracle_wasm_hex("we_fence_i32", &src);
    assert!(!oracle.is_empty(), "the oracle accepts Vec<i32>");
    let shadow = mnexp_hex(&src);
    assert!(
        shadow.contains("!!"),
        "W-ELEM fence: a narrow elem must POISON loud, never default a width"
    );
}

/// W-ELEM determinism.
#[test]
fn welem_deterministic() {
    assert_corpus_deterministic("W-ELEM", &welem_corpus());
}

// ── W-MOD: mn_expand module descent ───────────────────────────────────────────────────────
// A multi-module input parses to a P_K_PROGRAM root whose direct children are MODULE nodes;
// pre-W-MOD mn_expand scanned the root's DIRECT children for items, found none, and silently
// no-opped (zero instances, zero 2^21 flags) — the composed-context poison root cause. Now
// mn_collect_modules drives every builder/table/walk per module; instances append to the
// FIRST module (the oracle's drain target, the MONO-0 pin).

fn wmod_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let tool_body = format!(
        "module tool;\n{vecsrc}\nfn g(v: Vec<i64>) -> i64 {{ let x: i64 = v.get(0); return x; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<i64> = Vec::new(); let q: i64 = v.push(41); return 0 - g(v); }}\n"
    );
    let single = tool_body.clone();
    // one extra trivial module flips the root to P_K_PROGRAM — the sole variable.
    let two_mod =
        format!("{tool_body}module extra;\npub fn helper(a: i64) -> i64 {{ return a + 1; }}\n");
    // three modules + a generic record USE in the first module (mn_expand_records descent).
    let vecsrc2 = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let three_mod = format!(
        "module tool;\n{vecsrc2}\nrecord PN {{ kind: i64, cs: i64 }}\nfn g(nodes: Vec<PN>) -> i64 {{ let n: PN = nodes.get(0); return n.kind; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<PN> = Vec::new(); let q: i64 = v.push(PN {{ kind: 41, cs: 0 }}); return 0 - g(v); }}\nmodule extra;\npub fn helper(a: i64) -> i64 {{ return a + 1; }}\nmodule more;\npub fn helper2(a: i64) -> i64 {{ return a + 2; }}\n"
    );
    vec![
        ("wmod_single", single),
        ("wmod_two_mod", two_mod),
        ("wmod_three_mod_rec", three_mod),
    ]
}

/// W-MOD: whole-module byte parity — the module count must not change the bytes' correctness.
#[test]
fn wmod_byte_parity() {
    assert_module_parity("W-MOD", &wmod_corpus());
}

/// W-MOD execution capstone: the multi-module program RUNS on the shadow bytes to -41.
#[test]
fn wmod_exec_capstone() {
    let corpus = wmod_corpus();
    let source = corpus_source(&corpus, "wmod_two_mod");
    assert_execution_magnitude("W-MOD", "wmod_exec", source, 41);
}

/// W-MOD determinism.
#[test]
fn wmod_deterministic() {
    assert_corpus_deterministic("W-MOD", &wmod_corpus());
}

// ── W-STR-FIELD: str methods on a one-hop FIELD receiver ─────────────────────────────────
// `rn.text.bytes_eq(x)` / `.len()` / `.byte_at(i)` / `.substr(a,b)` / the desugar methods on
// an env-record base with a TC_T_STR field. The gate is the NO-EMIT cv_str_receiver_ok
// (2=field / 1=bare / 0=fall-through); each arm freshes its dst FIRST, then materializes the
// receiver (a field hop = the reg1 LoadField-Ptr temp via cv_to_var), then the args — the
// pinned oracle order, which ALSO fixed a latent bare divergence (return-position byte_at
// with a literal arg freshed the arg before the dst; the oracle freshes dst first).

fn wsf_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let arenasrc = strip_module(include_str!("../../../stdlib/sigil/arena.sigil"), "arena");
    let strdecl = "module strings;\npub fn str_bytes_eq(a: str, b: str) -> bool { let la: i64 = a.len(); let lb: i64 = b.len(); if la == lb { return true; } else { return false; } }\n";
    let strcat = "module string;\npub fn str_concat(a: str, b: str) -> str { return a; }\n";
    let pre = format!("module tool;\n{vecsrc}\n{arenasrc}\nrecord PS {{ kind: i64, text: str }}\n");
    vec![
        // the latent bare fixes (return-position literal args; oracle freshes dst first).
        (
            "wsf_bare_byteat_lit",
            format!(
                "{pre}fn g(s: str) -> i64 {{ return s.byte_at(1); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - g(\"ab\"); }}\n"
            ),
        ),
        (
            "wsf_bare_substr_lit",
            format!(
                "{pre}fn g(s: str) -> i64 {{ let r: str = s.substr(1, 3); return r.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(\"abcde\") + 39); }}\n"
            ),
        ),
        // the four field-receiver intrinsic/desugar methods.
        (
            "wsf_field_len",
            format!(
                "{pre}fn g(n: PS) -> i64 {{ return n.text.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let p: PS = PS {{ kind: 1, text: \"abc\" }}; return 0 - (g(p) + 38); }}\n"
            ),
        ),
        (
            "wsf_field_byteat",
            format!(
                "{pre}fn g(n: PS) -> i64 {{ return n.text.byte_at(1); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let p: PS = PS {{ kind: 1, text: \"ab\" }}; return 0 - g(p); }}\n"
            ),
        ),
        (
            "wsf_field_substr",
            format!(
                "{pre}fn g(n: PS) -> i64 {{ let r: str = n.text.substr(1, 3); return r.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let p: PS = PS {{ kind: 1, text: \"abcde\" }}; return 0 - (g(p) + 39); }}\n"
            ),
        ),
        (
            "wsf_field_byteseq",
            format!(
                "{pre}fn g(n: PS) -> i64 {{ let e: bool = n.text.bytes_eq(\"ab\"); if e {{ return 41; }} else {{ return 40; }} }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let p: PS = PS {{ kind: 1, text: \"ab\" }}; return 0 - g(p); }}\n{strdecl}"
            ),
        ),
        // the desugar CALL path on a field receiver (concat -> string::str_concat, receiver arg0).
        (
            "wsf_field_concat",
            format!(
                "{pre}fn g(n: PS) -> i64 {{ let r: str = n.text.concat(\"x\"); return r.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let p: PS = PS {{ kind: 1, text: \"abc\" }}; return 0 - (g(p) + 38); }}\n{strcat}"
            ),
        ),
        // the helper-style shape (annotated-let Vec<str> field extraction) stays byte-identical.
        (
            "wsf_vecfield_let",
            format!(
                "{pre}record TR {{ fnames: Vec<str> }}\nfn g(rec: TR) -> i64 {{ let fns: Vec<str> = rec.fnames; let n: i64 = fns.len(); let s: str = fns.get(0); return n + s.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<str> = Vec::new(); let q: i64 = v.push(\"abc\"); let r: TR = TR {{ fnames: v }}; return 0 - (g(r) + 37); }}\n"
            ),
        ),
    ]
}

/// W-STR-FIELD: whole-module byte parity across the field-receiver corpus.
#[test]
fn wsf_byte_parity() {
    assert_module_parity("W-STR-FIELD", &wsf_corpus());
}

/// W-STR-FIELD execution capstone: the field-receiver bytes RUN. len(abc)=3 + 38 -> -41.
#[test]
fn wsf_exec_capstone() {
    let corpus = wsf_corpus();
    let source = corpus_source(&corpus, "wsf_field_len");
    assert_execution_magnitude("W-STR-FIELD", "wsf_exec", source, 41);
}

/// W-STR-FIELD determinism.
#[test]
fn wsf_deterministic() {
    assert_corpus_deterministic("W-STR-FIELD", &wsf_corpus());
}

// ── W-STRRAW: str_from_raw intrinsic W-lane emission ─────────────────────────────────────
// str_from_raw(ptr, len) is a stdlib-PRIVATE str-header intrinsic (module `string`) that
// every string builder calls (str_concat/join/from_bytes/itoa/parse_*). The W-lane's
// cv_emit_vecintr dispatched alloc/vec_load/vec_store/store8 but NOT str_from_raw, so all of
// them poisoned. Emit = the string-LITERAL header shape with a RUNTIME ptr (air.rs:3082):
// WrapI64 data_ptr, WrapI64 len, BumpAlloc(dst,8,4), SF ptr@0, SF len@4. The exerciser lives
// in `module string` (str_from_raw is private there); the W-lane emits its body regardless of
// whether `tool` calls it, so the emitted-body byte-identity is the proof.

fn wsr_corpus() -> Vec<(&'static str, String)> {
    vec![
        // str_from_raw over a locally-built buffer (alloc + store8 + the intrinsic).
        ("wsr_body", "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 41; }\nmodule string;\npub fn mk3() -> str ! { Alloc } { let buf: i64 = alloc(3); store8(buf + 0, 97); store8(buf + 1, 98); store8(buf + 2, 99); return str_from_raw(buf, 3); }\n".to_string()),
        // str_from_raw over a param ptr + a literal len (the minimal intrinsic shape).
        ("wsr_body_param", "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 41; }\nmodule string;\npub fn wrap(buf: i64) -> str ! { Alloc } { return str_from_raw(buf, 3); }\n".to_string()),
        // str_from_raw with a VARIABLE len (both args runtime i64) + a fill loop.
        ("wsr_body_varlen", "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 41; }\nmodule string;\npub fn mkn(n: i64) -> str ! { Alloc } { let buf: i64 = alloc(n); let mut i: i64 = 0; while i < n { store8(buf + i, 120); i = i + 1; } return str_from_raw(buf, n); }\n".to_string()),
        // str_from_raw result let-bound then returned (dstgiven path).
        ("wsr_body_letret", "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 41; }\nmodule string;\npub fn mk(buf: i64, n: i64) -> str ! { Alloc } { let s: str = str_from_raw(buf, n); return s; }\n".to_string()),
    ]
}

/// W-STRRAW: the emitted str_from_raw body is byte-identical to the oracle (the string builders
/// were poison-free-but-unverified until now; this pins the ACTUAL bytes, not just non-poison).
#[test]
fn wsr_byte_parity() {
    assert_module_parity("W-STRRAW", &wsr_corpus());
}

/// W-STRRAW determinism.
#[test]
fn wsr_deterministic() {
    assert_corpus_deterministic("W-STRRAW", &wsr_corpus());
}

// ── W-FIELDVEC: Vec methods on a CONCRETE record's generic field
// AG-G19 closed: `rec.fnames.get(i)` (rec a CONCRETE record, fnames: Vec<str>) resolves —
// mn_field_targs skips the base-targs requirement for a concrete base (its field-type leaves
// are already concrete), the record-def table holds ALL records (B-ASSOC guarded generic-only),
// and mn_expand_records PREPENDS its cloned defs so rewritten field annotations are
// backward-declared for tc_build_recs (the empirically-found MONO-6 order interaction).

fn wfv_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let pre = format!(
        "module tool;\n{vecsrc}\nrecord TR {{ fnames: Vec<str>, ftags: Vec<i64> }}\nfn feed() -> TR {{ let mut v: Vec<str> = Vec::new(); let q1: i64 = v.push(\"abc\"); let mut t: Vec<i64> = Vec::new(); let q2: i64 = t.push(41); return TR {{ fnames: v, ftags: t }}; }}\n"
    );
    vec![
        // a PARAM-bound concrete base, str-elem get (the tc_find_field shape).
        (
            "wfv_param_strget",
            format!(
                "{pre}fn g(rec: TR, i: i64) -> i64 {{ let s: str = rec.fnames.get(i); return s.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let r: TR = feed(); return 0 - (g(r, 0) + 38); }}\n"
            ),
        ),
        // an ANNOTATED-LET-bound base, field .len().
        (
            "wfv_let_len",
            format!(
                "{pre}fn g(rec0: TR) -> i64 {{ let rec: TR = rec0; let n: i64 = rec.ftags.len(); return n; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let r: TR = feed(); return 0 - (g(r) + 40); }}\n"
            ),
        ),
        // i64-elem field get (the rec.ftags shape; W-ELEM elem discrimination through the field).
        (
            "wfv_i64get",
            format!(
                "{pre}fn g(rec: TR) -> i64 {{ let v0: i64 = rec.ftags.get(0); return v0; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let r: TR = feed(); return 0 - g(r); }}\n"
            ),
        ),
        // the exact tc_find_field body shape (loop + both fields + early return).
        (
            "wfv_findfield",
            format!(
                "{pre}fn find(rec: TR, want: i64) -> i64 {{ let n: i64 = rec.fnames.len(); let mut i: i64 = 0; while i < n {{ let nm: str = rec.fnames.get(i); if nm.len() == want {{ return rec.ftags.get(i); }} else {{ }} i = i + 1; }} return 0 - 1; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let r: TR = feed(); return 0 - find(r, 3); }}\n"
            ),
        ),
    ]
}

/// W-FIELDVEC: whole-module byte parity.
#[test]
fn wfv_byte_parity() {
    assert_module_parity("W-FIELDVEC", &wfv_corpus());
}

/// W-FIELDVEC execution capstone: the tc_find_field shape RUNS on the shadow bytes.
/// find(r, 3): fnames[0]="abc" (len 3 == want) -> ftags[0] = 41 -> -41.
#[test]
fn wfv_exec_capstone() {
    let corpus = wfv_corpus();
    let source = corpus_source(&corpus, "wfv_findfield");
    assert_execution_magnitude("W-FIELDVEC", "wfv_exec", source, 41);
}

/// W-FIELDVEC determinism.
#[test]
fn wfv_deterministic() {
    assert_corpus_deterministic("W-FIELDVEC", &wfv_corpus());
}

// ── W-INTOCONST: a const reference as an assignment RHS ──────────────────────────────────
// `op = T_PLUS;` — a top-level const as the whole assign value — poisoned: W-CONST added the
// const fallback to cv_to_var's bare-path arm but cv_into (the given-dst path every ASSIGN
// takes) never got it, so the entire parser-binop/tc-emit/tt/mn cluster (25 fns whose bodies
// are otherwise fully handled shapes) poisoned on their `op = T_KIND` selections. The fix
// mirrors cv_to_var's fallback: env miss -> variant miss -> const hit -> Assign dst IntLit.

fn wic_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let arenasrc = strip_module(include_str!("../../../stdlib/sigil/arena.sigil"), "arena");
    let pre = format!(
        "module tool;\n{vecsrc}\n{arenasrc}\nrecord Token {{ kind: i64, start: i64, end: i64, value: i64 }}\nrecord PNode {{ kind: i64, start: i64, end: i64, value: i64, flags: i64, child_start: i64, child_count: i64, text: str }}\nconst T_PLUS: i64 = 1;\nconst T_MINUS: i64 = 2;\n"
    );
    let minimal = format!(
        "{pre}fn g(x: i64) -> i64 {{ let mut op: i64 = 0;\n    if x < 3 {{\n        op = T_PLUS;\n    }} else {{\n    }}\n    return op;\n}}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{ return 0 - (g(1) + 40); }}\n"
    );
    let helpers = "fn mk_binary(op: i64, lhs: i64, rhs: i64, nodes: Arena<PNode> @Mut, kids: Vec<i64> @Mut) -> i64 ! { Alloc } {\n    let c0: i64 = kids.push(lhs);\n    let c1: i64 = kids.push(rhs);\n    let cs: i64 = kids.len() - 2;\n    let id: i64 = nodes.allocate(PNode { kind: op, start: 0, end: 0, value: 0, flags: 0, child_start: cs, child_count: 2, text: \"\" });\n    return id;\n}\nfn prim(src: str, toks: Vec<Token>, pos: i64, nodes: Arena<PNode> @Mut, kids: Vec<i64> @Mut) -> (i64, i64) ! { Alloc } {\n    let t: Token = toks.get(pos);\n    let id: i64 = nodes.allocate(PNode { kind: 99, start: t.start, end: t.end, value: t.value, flags: 0, child_start: 0, child_count: 0, text: \"\" });\n    return (id, pos + 1);\n}\n";
    let additive = "fn additive(src: str, toks: Vec<Token>, pos: i64, nodes: Arena<PNode> @Mut, kids: Vec<i64> @Mut) -> (i64, i64) ! { Alloc } {\n    let (first, p1) = prim(src, toks, pos, nodes, kids);\n    let mut lhs: i64 = first;\n    let mut p: i64 = p1;\n    let mut going: bool = true;\n    while going {\n        let t: Token = toks.get(p);\n        let mut op: i64 = 0;\n        if t.kind == T_PLUS {\n            op = T_PLUS;\n        } else {\n        }\n        if t.kind == T_MINUS {\n            op = T_MINUS;\n        } else {\n        }\n        if op > 0 {\n            let (rhs, p2) = prim(src, toks, p + 1, nodes, kids);\n            lhs = mk_binary(op, lhs, rhs, nodes, kids);\n            p = p2;\n        } else {\n            going = false;\n        }\n    }\n    return (lhs, p);\n}\n";
    let drv = "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n    let mut toks: Vec<Token> = Vec::new();\n    let q1: i64 = toks.push(Token { kind: 0, start: 0, end: 0, value: 40 });\n    let q2: i64 = toks.push(Token { kind: 1, start: 0, end: 0, value: 0 });\n    let q3: i64 = toks.push(Token { kind: 0, start: 0, end: 0, value: 1 });\n    let q4: i64 = toks.push(Token { kind: 9, start: 0, end: 0, value: 0 });\n    let mut nodes: Arena<PNode> = Arena::new();\n    let mut kids: Vec<i64> = Vec::new();\n    let (root, pend) = additive(\"x\", toks, 0, nodes, kids);\n    let rn: PNode = nodes.get(root);\n    return 0 - (rn.kind + pend + 38);\n}\n";
    vec![
        // the minimal shape: a const as an assign RHS in a nested block.
        ("wic_assign_const", minimal),
        // the VERBATIM parser_additive replica (mini prim/mk_binary): the real cluster shape.
        (
            "wic_parser_additive",
            format!("{pre}{helpers}{additive}{drv}"),
        ),
    ]
}

/// W-INTOCONST: whole-module byte parity.
#[test]
fn wic_byte_parity() {
    assert_module_parity("W-INTOCONST", &wic_corpus());
}

/// W-INTOCONST execution capstone: the parser_additive replica RUNS on the shadow bytes.
/// tokens [v40, T_PLUS, v1, end]: binary(T_PLUS) node, pend=3 -> -(1 + 3 + 38) = -42.
#[test]
fn wic_exec_capstone() {
    let corpus = wic_corpus();
    let source = corpus_source(&corpus, "wic_parser_additive");
    assert_execution_magnitude("W-INTOCONST", "wic_exec", source, 42);
}

/// W-INTOCONST determinism.
#[test]
fn wic_deterministic() {
    assert_corpus_deterministic("W-INTOCONST", &wic_corpus());
}

// ── W-FIELDITOA: .itoa on a one-hop I64 field receiver ───────────────────────────────────
// `tv.value.itoa()` — the parser_const/parser_emit/encode/tc_tmangle_kind/tc_emit_expr shape.
// W-STR-FIELD (#555) extended the wantstr desugar methods to field receivers but kept itoa
// bare-I64-only (AG-WSF3); this closes it: the gate accepts a one-hop field whose ftag token
// is I64 (cv_field_tok), and the receiver materializes via cv_to_var AFTER the dst — the
// same pinned (dst, receiver, args) order.

fn wfi_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let strdecl = "module string;\npub fn str_itoa(v: i64) -> str ! { Alloc } { let buf: i64 = alloc(1); store8(buf, 48); return str_from_raw(buf, 1); }\npub fn str_concat(a: str, b: str) -> str ! { Alloc } { return a; }\n";
    let pre = format!("module tool;\n{vecsrc}\nrecord Token {{ kind: i64, value: i64 }}\n");
    vec![
        // the bare-receiver control (W-STR-B; must stay byte-identical).
        (
            "wfi_bare",
            format!(
                "{pre}fn g(v: i64) -> i64 {{ let r: str = v.itoa(); return r.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(7) + 40); }}\n{strdecl}"
            ),
        ),
        // itoa on a one-hop I64 field receiver, let-bound (the parser_const shape).
        (
            "wfi_field_let",
            format!(
                "{pre}fn g(tv: Token) -> i64 {{ let r: str = tv.value.itoa(); return r.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let t: Token = Token {{ kind: 1, value: 7 }}; return 0 - (g(t) + 40); }}\n{strdecl}"
            ),
        ),
        // field itoa NESTED as a concat arg (the tc_emit_expr shape).
        (
            "wfi_field_nested_arg",
            format!(
                "{pre}fn g(tv: Token, s: str) -> i64 {{ let r: str = s.concat(tv.value.itoa()); return r.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let t: Token = Token {{ kind: 1, value: 7 }}; return 0 - (g(t, \"ab\") + 39); }}\n{strdecl}"
            ),
        ),
    ]
}

/// W-FIELDITOA: whole-module byte parity.
#[test]
fn wfi_byte_parity() {
    assert_module_parity("W-FIELDITOA", &wfi_corpus());
}

/// W-FIELDITOA fence (one-sided LOUD): itoa on a NON-i64 field (str) falls through -> the
/// ST-2 path misses -> poison, never a wrong-typed desugar call.
#[test]
fn wfi_nonint_fence() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let src = format!(
        "module tool;\n{vecsrc}\nrecord PS {{ kind: i64, text: str }}\nfn g(n: PS) -> i64 {{ let r: str = n.text.itoa(); return r.len(); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let p: PS = PS {{ kind: 1, text: \"ab\" }}; return 0 - (g(p) + 40); }}\nmodule string;\npub fn str_itoa(v: i64) -> str ! {{ Alloc }} {{ let buf: i64 = alloc(1); store8(buf, 48); return str_from_raw(buf, 1); }}\n"
    );
    // the ORACLE rejects itoa on a str receiver (type error) — the shadow must not emit either.
    let oracle = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        oracle_wasm_hex("wfi_fence", &src)
    }));
    assert!(oracle.is_err(), "the oracle must reject str.itoa()");
    let shadow = mnexp_hex(&src);
    assert!(
        shadow.contains("!!"),
        "W-FIELDITOA fence: a non-i64 field receiver must POISON loud"
    );
}

/// W-FIELDITOA determinism.
#[test]
fn wfi_deterministic() {
    assert_corpus_deterministic("W-FIELDITOA", &wfi_corpus());
}

// ── W-TUPELEM: the $str sentinel on tuple-destructured elements ──────────────────────────────
// `let (btext, bend, bp) = parser_pat_bindings(…); btext.len()` — the parser_pattern /
// parser_extern shape (the LAST two compiler fns in the census). The call-RHS destructure now
// rides the per-element provenance sentinel (cv_tupelems_of_mangle, atom-set-locked to
// cv_tuptys_of_mangle), so a destructured str binding is CvBind-identical to an annotated str
// let and the W-STR-A/B/FIELD gates just work. Arg/construct uses were already byte-correct
// (parser_fn's clean shape — it masked the class) — the control pins they stay so.

fn wte_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let pre = format!("module tool;\n{vecsrc}\nrecord PS {{ t: str }}\n");
    let hlp =
        "fn h(s: str, pos: i64) -> (str, i64, i64) ! { Alloc } { return (s, pos, pos + 1); }\n";
    let strmods = "module string;\npub fn str_concat(a: str, b: str) -> str { return a; }\n";
    vec![
        // a str INTRINSIC (len) on a tuple-destructured receiver (the parser_pattern shape).
        (
            "wte_len",
            format!(
                "{pre}{hlp}fn g(s: str) -> i64 !{{ Alloc }} {{ let (a, b, c) = h(s, 1); return a.len() + b + c; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(\"abc\") + 36); }}\n"
            ),
        ),
        // parser_extern's exact shape: substr with a NESTED len, both on the destructured str.
        (
            "wte_substr_nested",
            format!(
                "{pre}{hlp}fn g(s: str) -> i64 !{{ Alloc }} {{ let (a, b, c) = h(s, 1); let r: str = a.substr(2, a.len()); return r.len() + b + c; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(\"abcdef\") + 35); }}\n"
            ),
        ),
        // the desugar CALL path (concat -> string::str_concat) on a destructured receiver.
        (
            "wte_concat_desugar",
            format!(
                "{pre}{hlp}fn g(s: str) -> i64 !{{ Alloc }} {{ let (a, b, c) = h(s, 1); let r: str = a.concat(\"x\"); return r.len() + b + c; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(\"abc\") + 36); }}\n{strmods}"
            ),
        ),
        // the parser_fn CONTROL: destructured str as ARG + construct field only (was already
        // byte-correct pre-fix; pins no-regression on the masked shape).
        (
            "wte_arg_construct_control",
            format!(
                "{pre}{hlp}fn g(s: str) -> i64 !{{ Alloc }} {{ let (a, b, c) = h(s, 1); let w: str = s.concat(a); let r: PS = PS {{ t: a }}; return b + c; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(\"abc\") + 39); }}\n{strmods}"
            ),
        ),
    ]
}

/// W-TUPELEM: whole-module byte parity.
#[test]
fn wte_byte_parity() {
    assert_module_parity("W-TUPELEM", &wte_corpus());
}

/// W-TUPELEM fence (one-sided LOUD, AG-WTE1): the PATH-RHS destructure (a tuple LOCAL) keeps
/// elem:"" -> a str method on its element stays fall-through POISON, never wrong bytes.
#[test]
fn wte_fence_path_rhs() {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let src = format!(
        "module tool;\n{vecsrc}\nfn h(s: str, pos: i64) -> (str, i64) ! {{ Alloc }} {{ return (s, pos); }}\nfn g(s: str) -> i64 !{{ Alloc }} {{ let p: (str, i64) = h(s, 1); let (a, b) = p; return a.len() + b; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(\"abc\") + 38); }}\n"
    );
    let oracle = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        oracle_wasm_hex("wte_fence", &src)
    }));
    assert!(
        oracle.is_ok(),
        "the oracle accepts the path-RHS destructure"
    );
    let shadow = mnexp_hex(&src);
    assert!(
        shadow.contains("!!"),
        "W-TUPELEM fence: a path-RHS destructured str receiver must POISON loud"
    );
}

/// W-TUPELEM execution capstone: the nested-substr bytes RUN. substr(2, len=6)="cdef" -> 4,
/// +b(1)+c(2)=7, +35 -> -42.
#[test]
fn wte_exec_capstone() {
    let corpus = wte_corpus();
    let source = corpus_source(&corpus, "wte_substr_nested");
    assert_execution_magnitude("W-TUPELEM", "wte_exec", source, 42);
}

/// W-TUPELEM determinism.
#[test]
fn wte_deterministic() {
    assert_corpus_deterministic("W-TUPELEM", &wte_corpus());
}

// ── W-VECBOOL: bool Vec elements in the closed elem set ───────────────────────────────────
// The source's ONE Vec<bool> use (`arglits` in tc_emit_call — per-arg int-literal flags).
// Probe-pinned: bool elems are i32-CLASS (plain 0x28/0x36 + align 2 at slot stride 8, NO
// byte-width ops; instance fn types carry 0x7f) — the wa fall-through already emits exactly
// that, so the fix is the one bool -> "Bool" arm in cv_vec_elem_tok. The narrow fence
// repointed to Vec<i32> (still outside the set, still LOUD).

fn wvb_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let pre = format!("module tool;\n{vecsrc}\n");
    vec![
        // the tc_emit_call shape: literal pushes + get + branch.
        (
            "wvb_arglits",
            format!(
                "{pre}fn g(x: i64) -> i64 !{{ Alloc }} {{ let mut arglits: Vec<bool> = Vec::new(); let q1: i64 = arglits.push(true); let q2: i64 = arglits.push(false); let b: bool = arglits.get(0); if b {{ return x + 1; }} else {{ return x; }} }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(40) + 1); }}\n"
            ),
        ),
        // a bool LOCAL flows through push (the env-token store-value channel).
        (
            "wvb_boollocal",
            format!(
                "{pre}fn g(x: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<bool> = Vec::new(); let t: bool = true; let q1: i64 = v.push(t); let b: bool = v.get(0); if b {{ return x + 2; }} else {{ return x; }} }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - g(40); }}\n"
            ),
        ),
    ]
}

/// W-VECBOOL: whole-module byte parity.
#[test]
fn wvb_byte_parity() {
    assert_module_parity("W-VECBOOL", &wvb_corpus());
}

/// W-VECBOOL execution capstone: the arglits bytes RUN. get(0)=true -> 41, -(41+1) = -42.
#[test]
fn wvb_exec_capstone() {
    let corpus = wvb_corpus();
    let source = corpus_source(&corpus, "wvb_arglits");
    assert_execution_magnitude("W-VECBOOL", "wvb_exec", source, 42);
}

/// W-VECBOOL determinism.
#[test]
fn wvb_deterministic() {
    assert_corpus_deterministic("W-VECBOOL", &wvb_corpus());
}

// ── CAP-INIT: the synthesized module init ─────────────────────────────────────────────────
// The oracle synthesizes `{module}__init` (type 60 00 00, code 03 00 0f 0b, no fuel
// prologue) for any module whose typed-function list is EMPTY — an all-generic module, a
// record-only module, or an empty one. The shadow's module walk now synthesizes it
// positionally at stage >= 3. In the capstone input this is `option__init` — the fix took
// the Stage-1 vs Stage-2 gap from 74 to 47 bytes with every non-code section byte-EQUAL.

fn wci_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let pre = format!(
        "module tool;\n{vecsrc}\nfn g(x: i64) -> i64 {{ return x + 1; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(40) + 1); }}\n"
    );
    vec![
        // an ALL-GENERIC module (the option.sigil shape): zero emitted fns -> init.
        (
            "wci_generic_only",
            format!("{pre}module allgen;\npub fn idg<T>(x: T) -> T {{ return x; }}\n"),
        ),
        // a RECORD-only module: zero fns -> init.
        (
            "wci_record_only",
            format!("{pre}module recs;\nrecord RR {{ a: i64 }}\n"),
        ),
    ]
}

/// CAP-INIT: whole-module byte parity — the synthesized init lands at the oracle's
/// position with the oracle's bytes.
#[test]
fn wci_byte_parity() {
    assert_module_parity("CAP-INIT", &wci_corpus());
}

/// CAP-INIT execution capstone: the module with a synthesized init RUNS. g(40)+1 -> -42.
#[test]
fn wci_exec_capstone() {
    let corpus = wci_corpus();
    let source = corpus_source(&corpus, "wci_generic_only");
    assert_execution_magnitude("CAP-INIT", "wci_exec", source, 42);
}

/// CAP-INIT determinism.
#[test]
fn wci_deterministic() {
    assert_corpus_deterministic("CAP-INIT", &wci_corpus());
}

// ── CAP-LOCALS: field-str intrinsics in EXPRESSION position ───────────────────────────────
// `if sig.ret_detail.len() > 0` (cv_sig_ret_tok), `if b.fields.len() > 0` (tt_lookup_field),
// tc_emit_call — cv_expr_tytok's method arm gated the intrinsic ret tokens on a BARE $str
// receiver only, so a field-str .len() in an if condition freshed its temp from the
// fall-through token (Ptr, 0x7f) where the oracle has I64 (0x7e): a same-length SILENT
// locals-width divergence, invisible to the poison census. The gate now mirrors
// cv_str_receiver_ok's one-hop field arm (cv_field_isstr). Let-bound / return positions
// were always immune (dst from the annotation / fn ret) — the control pins that.

fn wcl_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let pre = format!("module tool;\n{vecsrc}\nrecord PS {{ kind: i64, text: str }}\n");
    vec![
        // the divergent shape: field-str .len() in an IF CONDITION.
        (
            "wcl_fieldlen_cond",
            format!(
                "{pre}fn g(n: PS) -> i64 !{{ Alloc }} {{ if n.text.len() > 0 {{ return 41; }} else {{ return 40; }} }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let p: PS = PS {{ kind: 1, text: \"ab\" }}; return 0 - (g(p) + 1); }}\n"
            ),
        ),
        // the immune control: let-bound field-str len then compare.
        (
            "wcl_fieldlen_let",
            format!(
                "{pre}fn g(n: PS) -> i64 !{{ Alloc }} {{ let l: i64 = n.text.len(); if l > 0 {{ return 41; }} else {{ return 40; }} }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let p: PS = PS {{ kind: 1, text: \"ab\" }}; return 0 - (g(p) + 1); }}\n"
            ),
        ),
    ]
}

/// CAP-LOCALS: whole-module byte parity.
#[test]
fn wcl_byte_parity() {
    assert_module_parity("CAP-LOCALS", &wcl_corpus());
}

/// CAP-LOCALS execution capstone: the condition-position bytes RUN. len("ab")>0 -> 41 -> -42.
#[test]
fn wcl_exec_capstone() {
    let corpus = wcl_corpus();
    let source = corpus_source(&corpus, "wcl_fieldlen_cond");
    assert_execution_magnitude("CAP-LOCALS", "wcl_exec", source, 42);
}

/// CAP-LOCALS determinism.
#[test]
fn wcl_deterministic() {
    assert_corpus_deterministic("CAP-LOCALS", &wcl_corpus());
}

// ── CAP-ENUM scalar: the generic-enum instance cell size ──────────────────────────────────
// `return Some(x)` at Option<i64> — the generic def sizes T payloads at width 4, so the
// ctor under-allocated 8 where the oracle's instance cell is 12 (stores were always
// arg-token-correct: a SILENT wrong-size alloc, ndiff=1 per module). The ctor now sizes
// max(def size, 4 + actual arg widths): concrete enums byte-UNCHANGED (def size already
// the variant max), None untouched (unit ctors don't alloc here).

fn wce_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let optsrc = strip_module(include_str!("../../../stdlib/sigil/option.sigil"), "option");
    let pre = format!("module tool;\n{vecsrc}\n{optsrc}\n");
    vec![
        // return-position Some + None at Option<i64> (the str_find shape).
        (
            "wce_ret_some_none",
            format!(
                "{pre}fn f(x: i64) -> Option<i64> !{{ Alloc }} {{ if x > 0 {{ return Some(x); }} else {{ }} return None; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let o: Option<i64> = f(41); return 0 - 42; }}\n"
            ),
        ),
        // let-annotated ctor.
        (
            "wce_let_some",
            format!(
                "{pre}fn g(x: i64) -> i64 !{{ Alloc }} {{ let o: Option<i64> = Some(x); return x + 1; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(41) + 0); }}\n"
            ),
        ),
    ]
}

/// CAP-ENUM scalar: whole-module byte parity.
#[test]
fn wce_byte_parity() {
    assert_module_parity("CAP-ENUM", &wce_corpus());
}

/// CAP-ENUM execution capstone: the Some/None bytes RUN (-42).
#[test]
fn wce_exec_capstone() {
    let corpus = wce_corpus();
    let source = corpus_source(&corpus, "wce_ret_some_none");
    assert_execution_magnitude("CAP-ENUM", "wce_exec", source, 42);
}

/// CAP-ENUM determinism.
#[test]
fn wce_deterministic() {
    assert_corpus_deterministic("CAP-ENUM", &wce_corpus());
}

// ── CAP-MATCH: match-on-enum + the tuple-let copy re-pin ──────────────────────────────────
// The oracle's match chain (render-pinned): binder freshed FIRST, tag LF @0:I32, variant-
// index const (I32), Eq, Br m=next; the payload LF @4 in its own block, then the walked
// body. A bare ident naming a variant (`None =>`) parses as P_K_PAT_BINDING — resolved via
// cv_variant_find. The payload token rides the annotation lens (generic-enum instance ->
// targ token); generic-enum annotations type Ptr (ai_airtype_of_typenode); I32 operands
// join wa_op_byte's i32 domain (Eq only — sign-agnostic). The ST-3 temp+copy re-pinned to
// the DESTRUCTURE (the let binds the construct var directly — render-proven both shapes).
// The formerly-ORPHANED match fences (poison pushed after the flush mark) now fail LOUD.

fn wcm_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = strip_module(include_str!("../../../stdlib/sigil/vec.sigil"), "vec");
    let optsrc = strip_module(include_str!("../../../stdlib/sigil/option.sigil"), "option");
    let pre = format!(
        "module tool;\n{vecsrc}\n{optsrc}\nfn h(x: i64) -> Option<i64> !{{ Alloc }} {{ if x > 0 {{ return Some(x); }} else {{ }} return None; }}\n"
    );
    vec![
        (
            "wcm_match_let_scrut",
            format!(
                "{pre}fn g(x: i64) -> i64 !{{ Alloc }} {{ let pos: Option<i64> = h(x); let mut p: i64 = 0; let mut found: bool = false; match pos {{ Some(v) => {{ p = v; found = true; }}, None => {{ found = false; }}, }} if found {{ return p; }} else {{ return 0 - 1; }} }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - g(42); }}\n"
            ),
        ),
        (
            "wcm_let_only",
            format!(
                "{pre}fn g(x: i64) -> i64 !{{ Alloc }} {{ let pos: Option<i64> = h(x); return x + 1; }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - (g(41) + 0); }}\n"
            ),
        ),
        (
            "wcm_tuple_tail",
            format!(
                "{pre}fn t(a: str, b: str) -> Option<(str, str)> !{{ Alloc }} {{ let pair: (str, str) = (a, b); return Some(pair); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let o: Option<(str, str)> = t(\"a\", \"b\"); return 0 - 42; }}\n"
            ),
        ),
    ]
}

/// CAP-MATCH: whole-module byte parity.
#[test]
fn wcm_byte_parity() {
    assert_module_parity("CAP-MATCH", &wcm_corpus());
}

/// CAP-MATCH execution capstone: the match bytes RUN. h(42)=Some(42) -> p=42 -> -42.
#[test]
fn wcm_exec_capstone() {
    let corpus = wcm_corpus();
    let source = corpus_source(&corpus, "wcm_match_let_scrut");
    assert_execution_magnitude("CAP-MATCH", "wcm_exec", source, 42);
}

/// CAP-MATCH determinism.
#[test]
fn wcm_deterministic() {
    assert_corpus_deterministic("CAP-MATCH", &wcm_corpus());
}

// ── AG6-1: the fail-closed invariant (docs/specs/ag-6-full-emit.md) ─────────────────────────
// AG6-0 RUN-validated that MI-1 (a non-widest-variant generic-enum "silent under-alloc") does
// NOT exist today: every generic-enum shape the selfhost cannot size correctly POISONS
// (fail-closed) rather than emitting wrong bytes. This differential PINS that invariant so the
// AG6-3 un-fencing of generic-enum monomorphization cannot regress it: for every canary shape,
// the shadow is byte-identical to the oracle OR it poisons ("!!") — NEVER silently divergent.
// Today the un-instanced / method canaries all poison; as AG6-2/AG6-3 land they flip to
// byte-identical (EQ still satisfies the invariant). A shape that emits shadow != oracle without
// poisoning turns this RED — the exact silent fail-open MI-1 warned about.

fn ag6_fail_closed_corpus() -> Vec<(&'static str, String)> {
    let optsrc = strip_module(include_str!("../../../stdlib/sigil/option.sigil"), "option");
    let pre = format!("module tool;\n{optsrc}\n");
    vec![
        // widest-variant construct via generic-fn mono — byte-identical TODAY (the EQ branch).
        (
            "gfn_big_widest",
            "module tool;\nenum E<T> { Small(bool), Big(T) }\nfn wrap<T>(x: T) -> E<T> !{ Alloc } { return E::Big(x); }\nfn f() -> i64 !{ Alloc } { let e: E<i64> = wrap(7); return 1; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n".to_string(),
        ),
        // non-widest variant forced onto a wide instance via generic-fn mono — poisons TODAY.
        (
            "gfn_small_nonwidest",
            "module tool;\nenum E<T> { Small(bool), Big(T) }\nfn wrap<T>(x: bool) -> E<T> !{ Alloc } { return E::Small(x); }\nfn f() -> i64 !{ Alloc } { let e: E<i64> = wrap(true); return 1; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n".to_string(),
        ),
        // Result-shaped two-param enum, construct the Err (non-widest) side — poisons TODAY.
        (
            "result_err_side",
            "module tool;\nenum R<A, B> { Ok(A), Err(B) }\nfn mk<A, B>(b: B) -> R<A, B> !{ Alloc } { return R::Err(b); }\nfn f() -> i64 !{ Alloc } { let r: R<i64, bool> = mk(true); return 1; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n".to_string(),
        ),
        // the residual: the generic-enum METHOD unwrap_or at T=str — poisons TODAY (AG6-3 target).
        (
            "unwrap_or_str",
            format!("{pre}fn f() -> str !{{ Alloc }} {{ let o: Option<str> = Some(\"x\"); return o.unwrap_or(\"\"); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - 1; }}\n"),
        ),
        // unwrap_or at T=i64 — poisons TODAY.
        (
            "unwrap_or_i64",
            format!("{pre}fn f() -> i64 !{{ Alloc }} {{ let o: Option<i64> = Some(5); return o.unwrap_or(0); }}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ return 0 - f(); }}\n"),
        ),
    ]
}

/// AG6-1: for every generic-enum canary, the selfhost shadow is byte-identical to the oracle OR
/// it poisons — never silently divergent. Guards the MI-1 fail-open class fail-closed.
#[test]
fn ag6_fail_closed_invariant() {
    for (label, src) in &ag6_fail_closed_corpus() {
        let oracle = oracle_wasm_hex(label, src);
        assert!(
            oracle.len() > 100,
            "AG6-1 {label}: the oracle must produce a real module (got {} hex chars) — else the \
             invariant would pass vacuously",
            oracle.len()
        );
        let shadow = mnexp_hex(src);
        let eq = oracle == shadow;
        let poison = shadow.contains("!!");
        assert!(
            eq || poison,
            "AG6-1 fail-closed invariant VIOLATED for {label}: the shadow diverges from the oracle \
             WITHOUT poisoning — a SILENT fail-open (the MI-1 class). oracle_len={}, shadow_len={}",
            oracle.len(),
            shadow.len()
        );
    }
}

// ── AG6-2: multi-payload variant match (docs/specs/ag-6-full-emit.md, SC-A1) ────────────────
// The W-lane match walker emitted only unit + single-payload variant arms (payc<=1); a variant
// with 2+ payload fields bound in a match arm poisoned (fail-closed, air.sigil payc==1 gate).
// AG6-2 loops the payload binders at accumulating offsets (4 + Σ widths) into pre-allocated
// locals — byte-identical to the oracle — so an arbitrary user enum (SC-A1's requirement) can be
// matched with all its binders. Concrete enums only; generic multi-payload stays fenced.

fn ag6_multipayload_corpus() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "pair_i64",
            "module tool;\nenum P { Pair(i64, i64), Nil }\nfn f() -> i64 !{ Alloc } { let p: P = P::Pair(3, 4); let mut r: i64 = 0; match p { Pair(a, b) => { r = a + b; }, Nil => { r = 0 - 1; }, } return r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n",
        ),
        (
            "mixed_wd",
            "module tool;\nenum P { Two(i64, bool), Nil }\nfn f() -> i64 !{ Alloc } { let p: P = P::Two(9, true); let mut r: i64 = 0; match p { Two(a, b) => { if b { r = a; } else { } }, Nil => { }, } return r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n",
        ),
        (
            "triple",
            "module tool;\nenum P { Tri(i64, i64, i64), Nil }\nfn f() -> i64 !{ Alloc } { let p: P = P::Tri(1, 2, 3); let mut r: i64 = 0; match p { Tri(a, b, c) => { r = a + b + c; }, Nil => { }, } return r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n",
        ),
    ]
}

/// AG6-2: multi-payload variant match — whole-module byte parity + no poison.
#[test]
fn ag6_multipayload_match_parity() {
    assert_module_parity("AG6-2", &ag6_multipayload_corpus());
}

/// AG6-2 execution capstone: the multi-payload match bytes RUN. Pair(3,4) -> a+b=7 -> -7.
#[test]
fn ag6_multipayload_exec() {
    let corpus = ag6_multipayload_corpus();
    let source = corpus_source(&corpus, "pair_i64");
    assert_execution_magnitude("AG6-2", "ag6mp_exec", source, 7);
}

// ── AG6-2 fail-open fence: match edge shapes must be byte-EQ or POISON, never wrong bytes ────
// The bug sweep found a PRE-EXISTING fail-open: a match with 2+ binder-bearing arms diverged
// silently (two_single uses the untouched single-payload path). AG6-2 fences it (an mbindcount
// guard poisons the 2nd+ binder arm) — turning a silent fail-open into a loud poison — and fences
// wildcard payloads in multi arms. This differential pins the invariant: EQ or poison, never a
// silent divergence. (A byte-identical fix for 2+ binder arms — pre-allocating all arm binders
// in the oracle's order — is a scoped follow-up; today they fail closed.)
fn ag6_match_edge_corpus() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "mp_wild_one",
            "module tool;\nenum P { Pair(i64, i64), Nil }\nfn f() -> i64 !{ Alloc } { let p: P = P::Pair(3, 4); let mut r: i64 = 0; match p { Pair(a, _) => { r = a; }, Nil => { }, } return r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n",
        ),
        (
            "mp_wild_all",
            "module tool;\nenum P { Pair(i64, i64), Nil }\nfn f() -> i64 !{ Alloc } { let p: P = P::Pair(3, 4); let mut r: i64 = 0; match p { Pair(_, _) => { r = 5; }, Nil => { }, } return r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n",
        ),
        (
            "mp_two_single",
            "module tool;\nenum P { A(i64), B(i64) }\nfn f() -> i64 !{ Alloc } { let p: P = P::A(3); let mut r: i64 = 0; match p { A(a) => { r = a; }, B(b) => { r = 0 - b; }, } return r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n",
        ),
        (
            "mp_two_multi",
            "module tool;\nenum P { A(i64, i64), B(i64, i64) }\nfn f() -> i64 !{ Alloc } { let p: P = P::A(3, 4); let mut r: i64 = 0; match p { A(a, b) => { r = a + b; }, B(c, d) => { r = c - d; }, } return r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n",
        ),
        (
            "mp_single_then_multi",
            "module tool;\nenum P { One(i64), Two(i64, i64) }\nfn f() -> i64 !{ Alloc } { let p: P = P::Two(3, 4); let mut r: i64 = 0; match p { One(a) => { r = a; }, Two(b, c) => { r = b + c; }, } return r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n",
        ),
        (
            "mp_str_pair",
            "module tool;\nenum P { S(str, str), Nil }\nfn f() -> i64 !{ Alloc } { let p: P = P::S(\"a\", \"b\"); let mut r: i64 = 0; match p { S(a, b) => { r = a.len() + b.len(); }, Nil => { }, } return r; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{ Alloc } { return 0 - f(); }\n",
        ),
    ]
}

#[test]
fn ag6_match_no_fail_open() {
    for (label, src) in ag6_match_edge_corpus() {
        let oracle = oracle_wasm_hex(label, src);
        assert!(
            oracle.len() > 100,
            "AG6-2 {label}: oracle must be a real module"
        );
        let shadow = mnexp_hex(src);
        let eq = oracle == shadow;
        let poison = shadow.contains("!!");
        assert!(
            eq || poison,
            "AG6-2 fail-open at {label}: multi-payload match diverged from the oracle WITHOUT \
             poisoning (silent wrong bytes). o={}, s={}",
            oracle.len(),
            shadow.len()
        );
    }
}

#[test]
// AG6-3: generic-enum METHOD monomorphization. A mono'd generic-enum-method call — receiver
// resolution AND a match-on-self body — emits byte-identically through the selfhost W-lane.
// The fix (cv_rec_of_typenode) resolves a child-bearing generic-enum instance annotation
// (`Option<str>`) to its enum rdef index; records are pre-rewritten to a bare mangle so are
// unaffected. RED before the fix: EMETH/MMATCH/UNWRAP poisoned; RESULT is the arbitrary
// 2-type-param enum (SC-A1).
fn ag6_generic_enum_method_corpus() {
    let corpus = [
        ("ETAKE", "module m;
enum OptG<T> { SomeV(T), NoneV }
fn take(x: OptG<i64>) -> i64 { return 3; }
fn f() -> i64 { let o: OptG<i64> = OptG::SomeV(5); return take(o); }
"),
        ("EMETH", "module m;
enum OptG<T> { SomeV(T), NoneV }
impl OptG<T> { fn tag(self: OptG<T>) -> i64 { return 7; } }
fn f() -> i64 { let o: OptG<i64> = OptG::SomeV(5); return o.tag(); }
"),
        ("RMETH", "module m;
record BoxG<T> { val: T }
impl BoxG<T> { fn get(self: BoxG<T>) -> i64 { return 7; } }
fn f() -> i64 { let b: BoxG<i64> = BoxG { val: 5 }; return b.get(); }
"),
        ("RESULT", "module m;
enum Res<T, E> { Okv(T), Errv(E) }
impl Res<T, E> { fn is_ok(self: Res<T, E>) -> i64 { return 1; } }
fn f() -> i64 { let r: Res<i64, str> = Res::Okv(5); return r.is_ok(); }
"),
        ("MMATCH", "module m;
enum OptG<T> { SomeV(T), NoneV }
impl OptG<T> { fn tag(self: OptG<T>) -> i64 { match self { SomeV(v) => { return 1; }, NoneV => { return 0; } } } }
fn f() -> i64 { let o: OptG<i64> = OptG::SomeV(5); return o.tag(); }
"),
        ("UNWRAP", "module m;
enum Opt<T> { Somev(T), Nonev }
impl Opt<T> { fn unwrap_or(self: Opt<T>, d: T) -> T { match self { Somev(v) => { return v; }, Nonev => { return d; } } } }
fn f() -> str { let o: Opt<str> = Opt::Somev(\"hi\"); return o.unwrap_or(\"x\"); }
"),
    ];
    for (name, src) in corpus {
        let oracle = oracle_wasm_hex(name, src);
        let shadow = mnexp_hex(src);
        assert_ne!(
            shadow, "!!",
            "AG6-3 {name}: the selfhost W-lane POISONED a generic-enum method"
        );
        assert_eq!(
            shadow, oracle,
            "AG6-3 {name}: selfhost emit must be byte-identical to the oracle"
        );
    }
}

#[test]
// AG6-3 fail-closed fence (SC-A4): every generic-enum-method shape emits EQ-or-POISON, NEVER
// wrong bytes. A future edit that makes the class emit DIVERGENT bytes trips this loudly.
fn ag6_generic_enum_method_no_divergence() {
    let adversarial = [
        ("SPAYLOAD", "module m;
enum Bx<T> { W(T), N }
impl Bx<T> { fn g(self: Bx<T>) -> i64 { match self { W(v) => { return 1; }, N => { return 0; } } } }
fn f() -> i64 { let o: Bx<str> = Bx::W(\"hi\"); return o.g(); }
"),
        ("TWOPARAM_MATCH", "module m;
enum Res<T, E> { Okv(T), Errv(E) }
impl Res<T, E> { fn code(self: Res<T, E>) -> i64 { match self { Okv(v) => { return 1; }, Errv(e) => { return 2; } } } }
fn f() -> i64 { let r: Res<i64, str> = Res::Errv(\"bad\"); return r.code(); }
"),
        ("PAYLOAD_RET_I64", "module m;
enum OptG<T> { SomeV(T), NoneV }
impl OptG<T> { fn or0(self: OptG<T>, d: T) -> T { match self { SomeV(v) => { return v; }, NoneV => { return d; } } } }
fn f() -> i64 { let o: OptG<i64> = OptG::SomeV(5); return o.or0(9); }
"),
    ];
    for (name, src) in adversarial {
        let oracle = oracle_wasm_hex(name, src);
        let shadow = mnexp_hex(src);
        let ok = shadow == "!!" || shadow == oracle;
        assert!(
            ok,
            "AG6-3 fence {name}: shadow DIVERGED (wrong bytes) — must be EQ or POISON"
        );
    }
}

// ── PRESERVE-THE-MILESTONE: PIN-4 — the mechanical fence registry ─────────────────────────────
//
// docs/CLAIMS.md §E lists the emit surface's honest boundary. It USED to live as a prose table
// in an unmerged planning doc -- a DANGLING AUTHORITY this test asserted totality over while the
// file was not even in the tree (found by the PIN-6 claims audit). §E is in-tree and
// machine-checked by crates/sigil-runtime/tests/claims_ledger.rs.
// Prose is not a gate: several fenced constructs had NO test, so a fence deleted together with
// its guard left no trace. This registry makes the table mechanical.
//
// THE INVARIANT BEING PINNED IS *FAIL-CLOSED*, NOT "poisons". A hole may legitimately become
// byte-identical later (AG6-3 did exactly that for generic-enum methods). What must NEVER happen
// is DIVERGE: the selfhost emitting wrong-but-plausible bytes. So every row asserts
// EQ-or-POISON-or-ORACLE-REJECTS, and never DIVERGE.

#[derive(Debug, PartialEq)]
enum FenceVerdict {
    /// The oracle itself refuses the construct — not a selfhost emit hole at all.
    OracleRejects,
    /// The selfhost refuses to emit (loud `!!`) — fail-closed, the intended state of a hole.
    Poison,
    /// The selfhost emits byte-identically — the hole has been closed (a good outcome).
    ByteEqual,
    /// The selfhost emitted DIFFERENT bytes. This is the only forbidden outcome.
    Diverge,
}

/// Non-panicking oracle emit: returns None when the oracle rejects at parse/resolve/typecheck.
fn try_oracle_wasm_hex(src: &str) -> Option<String> {
    let source = SourceFile::new("<fence>", src);
    let (ast, pdiags) = parser::parse(&source);
    if !pdiags.is_empty() {
        return None;
    }
    let resolved = name_resolution::resolve(&ast).ok()?;
    let (typed, _) = type_check::check_with_options(&resolved, &CompileOptions::default()).ok()?;
    let lowered = air::lower(&typed);
    let (mem_p, _) = memory::lower(lowered);
    let (fuel_p, _) = fuel::insert(mem_p);
    let out = wasm::emit(&fuel_p);
    if out.outer.is_some() {
        return None;
    }
    Some(out.inner.iter().map(|b| format!("{b:02x}")).collect())
}

fn classify_fence(src: &str) -> FenceVerdict {
    let Some(oracle) = try_oracle_wasm_hex(src) else {
        return FenceVerdict::OracleRejects;
    };
    let shadow = mnexp_hex(src);
    if shadow.len() == 2 {
        FenceVerdict::Poison
    } else if shadow == oracle {
        FenceVerdict::ByteEqual
    } else {
        FenceVerdict::Diverge
    }
}

/// Every row of the known-holes table, as executable fixtures.
fn fence_registry() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "2plus_binder_arm_match(AG6-2b)",
            "module m;\nenum Fp { Fa(i64), Fb(i64) }\nfn f() -> i64 { let p: Fp = Fp::Fa(3); let mut r: i64 = 0; match p { Fa(a) => { r = a; }, Fb(b) => { r = 0 - b; }, } return r; }\n",
        ),
        (
            "guarded_match_arm",
            "module m;\nenum Fg { Ga(i64), Gb }\nfn f() -> i64 { let p: Fg = Fg::Ga(3); let mut r: i64 = 0; match p { Ga(a) if a > 0 => { r = 1; }, Gb => { r = 2; }, } return r; }\n",
        ),
        (
            "wildcard_payload_in_multi_arm",
            "module m;\nenum Fw { Pair(i64, i64), Wn }\nfn f() -> i64 { let p: Fw = Fw::Pair(1, 2); let mut r: i64 = 0; match p { Pair(a, _) => { r = a; }, Wn => { r = 0; }, } return r; }\n",
        ),
        (
            "string_literal_pattern_arm",
            "module m;\nfn f(s: str) -> i64 { let mut r: i64 = 0; match s { \"foo\" => { r = 1; }, _ => { r = 2; }, } return r; }\n",
        ),
        (
            "range_pattern_arm",
            // Was `1..5`. SIGIL range PATTERNS are inclusive-only (`..=`); the
            // exclusive spelling is not grammar, so the oracle rejected the
            // fixture and the row measured nothing about the selfhost.
            "module m;\nfn f(n: i64) -> i64 { let mut r: i64 = 0; match n { 1..=5 => { r = 1; }, _ => { r = 2; }, } return r; }\n",
        ),
        (
            "closure_capture",
            // Was Rust's `|x: i64| -> i64 { .. }`. A SIGIL closure is spelled
            // `fn(..) -> T { .. }`, so the oracle rejected the fixture on
            // syntax — not because closures are unsupported (they are not:
            // see tests/closure_capture.rs).
            "module m;\nfn f() -> i64 { let k: i64 = 2; let g = fn(x: i64) -> i64 { return x + k; }; return g(3); }\n",
        ),
        (
            "question_mark_option_try",
            "module m;\nfn g() -> Option<i64> { return Some(1); }\nfn f() -> Option<i64> { let v: i64 = g()?; return Some(v + 1); }\n",
        ),
        (
            "option_own_tp_combinator_map",
            "module m;\nfn f() -> i64 { let o: Option<i64> = Some(1); let m2: Option<i64> = o.map(|x: i64| -> i64 { return x + 1; }); return m2.unwrap_or(0); }\n",
        ),
        (
            "recursive_generic_enum",
            "module m;\nenum Lst<T> { Cons(T, Lst<T>), Nil }\nfn f() -> i64 { let l: Lst<i64> = Lst::Nil; return 1; }\n",
        ),
        (
            "u256_enum_payload",
            "module m;\nenum Fu { Uv(u256), Un }\nfn f() -> i64 { let u: Fu = Fu::Un; return 1; }\n",
        ),
    ]
}

/// PIN-4: no known hole may DIVERGE. A hole may poison (fail-closed), be oracle-rejected, or have
/// been closed to byte-equality — but the selfhost must never emit wrong-but-plausible bytes.
#[test]
fn pin_fence_registry_never_diverges() {
    let reg = fence_registry();
    // Registry totality: the executable registry must cover every row of the §8 prose table.
    assert_eq!(
        reg.len(),
        10,
        "PIN-4: the fence registry must cover every documented hole in docs/CLAIMS.md §E; \
         adding a hole to the table REQUIRES adding a fixture here"
    );
    // RATCHET (the repo's drift-ratchet idiom). PIN-4's FIRST RUN found a real fail-open:
    // constructing the NARROW (unit) variant of a generic enum whose other variant is
    // multi-payload emits an UNDER-SIZED cell (oracle 20 B vs selfhost 16 B) instead of failing
    // closed — verbatim the failure X-SIZE was written to prevent ("a size derived from only the
    // constructed variant's args ... never silently under-allocs"). AG6-0 concluded this class was
    // fail-CLOSED; it is not — the AG6-1 canary corpus never constructed the narrow variant.
    // It was RECORDED here, not hidden — and then FIXED (AG6-6, `cv_enum_inst_size`): the cell is
    // now sized from the annotation's resolved INSTANCE (4 + max over ALL variants of the
    // SUBSTITUTED payload widths), so the ratchet stands at ZERO. Every row of the registry is now
    // OracleRejects, Poison, or ByteEqual — no row may EVER diverge again.
    // Regression canary for the fixed class: `ag6_6_narrow_variant_size_corpus`.
    const PIN4_KNOWN_DIVERGENCES: usize = 0;
    // No known divergence remains; this sentinel matches no fixture, so ANY divergence is reported.
    const PIN4_KNOWN_DIVERGENT: &str = "";
    let mut report: Vec<String> = Vec::new();
    let mut diverged: Vec<&str> = Vec::new();
    let mut unverified: Vec<&str> = Vec::new();
    for (name, src) in &reg {
        let v = classify_fence(src);
        report.push(format!("  {name:38} {v:?}"));
        if v == FenceVerdict::Diverge {
            diverged.push(name);
        }
        if v == FenceVerdict::OracleRejects {
            unverified.push(name);
        }
    }
    println!("PIN-4 fence registry:\n{}", report.join("\n"));
    // HONESTY PIN. `OracleRejects` does NOT mean "fence verified" — it means the fixture never
    // reached the selfhost, so that row is UNVERIFIED coverage. Several are almost certainly
    // malformed fixtures rather than unsupported features (SIGIL demonstrably HAS closures; see
    // tests/closure_capture.rs). Pin exact labels so one unverified row cannot silently replace
    // another while preserving a count.
    // `range_pattern_arm` and `closure_capture` were REMOVED from this list on
    // 2026-08-02: both were malformed fixtures (an exclusive `1..5` range
    // pattern, and Rust's `|x| ..` closure spelling), so the oracle rejected
    // them on syntax and the rows measured nothing. Rewritten in SIGIL's
    // grammar they now reach the selfhost and both measure Poison — real
    // fail-closed fences instead of unverified coverage.
    const PIN4_UNVERIFIED_FIXTURES: &[&str] =
        &["question_mark_option_try", "option_own_tp_combinator_map"];
    assert_eq!(
        unverified, PIN4_UNVERIFIED_FIXTURES,
        "PIN-4: the UNVERIFIED (oracle-rejected) fixture manifest moved. These rows prove nothing \
         about the selfhost; fix a fixture so the hole is exercised, then remove its label."
    );
    // The superseded prose table also claimed u256 enum payloads were FENCED;
    // this registry shows ByteEqual (the hole is closed). Prose is not a gate — this is.

    let unexpected: Vec<&&str> = diverged
        .iter()
        .filter(|n| **n != PIN4_KNOWN_DIVERGENT)
        .collect();
    assert!(
        unexpected.is_empty(),
        "PIN-4: NEW divergence — the selfhost emitted wrong-but-plausible bytes instead of failing \
         closed for {unexpected:?}. A known hole must fail CLOSED (loud poison); emitting DIFFERENT \
         bytes is the one forbidden outcome."
    );
    assert_eq!(
        diverged.len(),
        PIN4_KNOWN_DIVERGENCES,
        "PIN-4 RATCHET: the known-divergence count moved. If a hole was FIXED, ratchet \
         PIN4_KNOWN_DIVERGENCES DOWN in the same PR (that is a win — record it in the commit). \
         Never ratchet UP: a new fail-open must be fixed or fenced, not accepted."
    );
}

/// AG6-6 regression canary — the generic-enum NARROW-variant instance cell size.
///
/// The class PIN-4 caught: constructing a unit/narrow variant of a generic enum at a WIDTH-8 targ
/// under-allocated, because `cv_enum_total_size` sizes the UNSUBSTITUTED def (every type-param
/// slot counted at the placeholder width 4) and a unit ctor has no args for CAP-ENUM's
/// `4 + argw` term to correct from. MEASURED before the fix: oracle 20 B, selfhost 16 B.
///
/// BOTH directions are pinned. The width-4 rows (str / i32 / Ptr) are the shapes the compiler
/// itself uses — they must stay byte-identical, which is what makes the fix additive. The width-8
/// rows (i64) are the fix itself. Pinning only the latter would let an over-allocating "fix"
/// regress the certified surface silently.
#[test]
fn ag6_6_narrow_variant_size_corpus() {
    let shapes: Vec<(&str, &str)> = vec![
        // width-8 targ: the fixed rows (each of these DIVERGED before AG6-6).
        (
            "recursive/i64",
            "module m;
enum Lst<T> { Cons(T, Lst<T>), Nil }
fn f() -> i64 { let l: Lst<i64> = Lst::Nil; return 1; }
",
        ),
        (
            "multi-payload/i64",
            "module m;
enum E<T> { V(T, i64), N }
fn f() -> i64 { let e: E<i64> = E::N; return 1; }
",
        ),
        (
            "option-shape/i64",
            "module m;
enum O<T> { S(T), N }
fn f() -> i64 { let o: O<i64> = O::N; return 1; }
",
        ),
        // width-4 targ: the compiler's own shapes — byte-identical BEFORE and AFTER.
        (
            "recursive/str",
            "module m;
enum Lst<T> { Cons(T, Lst<T>), Nil }
fn f() -> i64 { let l: Lst<str> = Lst::Nil; return 1; }
",
        ),
        (
            "multi-payload/str",
            "module m;
enum E<T> { V(T, i64), N }
fn f() -> i64 { let e: E<str> = E::N; return 1; }
",
        ),
        (
            "option-shape/str",
            "module m;
enum O<T> { S(T), N }
fn f() -> i64 { let o: O<str> = O::N; return 1; }
",
        ),
        (
            "multi-payload/i32",
            "module m;
enum E<T> { V(T, i64), N }
fn f() -> i64 { let e: E<i32> = E::N; return 1; }
",
        ),
        // the WIDE variant construct: already covered by CAP-ENUM's `4 + argw`; pinned so the
        // instance-size path cannot regress the ctor path it now shares a cell size with.
        (
            "wide-ctor/i64",
            "module m;
enum E<T> { V(T, i64), N }
fn f() -> i64 { let e: E<i64> = E::V(7, 8); return 1; }
",
        ),
        // BARE unit variants (`N`, not `E::N`). SR-010 closed the production asymmetry that used
        // to discard the expected type arguments here; bare and qualified construction now
        // register and emit the same concrete layout.
        (
            "bare-unit/i64",
            "module m;
enum Lst<T> { Cons(T, Lst<T>), Nil }
fn f() -> i64 { let l: Lst<i64> = Nil; return 1; }
",
        ),
        (
            "bare-unit/option-i64",
            "module m;
enum O<T> { S(T), N }
fn f() -> i64 { let o: O<i64> = N; return 1; }
",
        ),
        (
            "bare-unit/option-str",
            "module m;
enum O<T> { S(T), N }
fn f() -> i64 { let o: O<str> = N; return 1; }
",
        ),
        (
            "bare-unit/mut-i64",
            "module m;
enum O<T> { S(T), N }
fn f() -> i64 { let mut o: O<i64> = N; return 1; }
",
        ),
        (
            "multi-param/qualified-unit",
            "module m;
enum Either<A, B> { L(A), R(B), N }
fn f() -> i64 { let e: Either<i32, i64> = Either::N; return 1; }
",
        ),
        (
            "multi-param/bare-unit",
            "module m;
enum Either<A, B> { L(A), R(B), N }
fn f() -> i64 { let e: Either<i32, i64> = N; return 1; }
",
        ),
        (
            "multi-param/narrow-payload",
            "module m;
enum Either<A, B> { L(A), R(B), N }
fn f() -> i64 { let e: Either<i32, i64> = Either::L(7); return 1; }
",
        ),
        (
            "return/qualified-unit",
            "module m;
enum E<T> { V(T, i64), N }
fn make() -> E<i64> { return E::N; }
fn f() -> i64 { let e: E<i64> = make(); return 1; }
",
        ),
        (
            "return/bare-unit",
            "module m;
enum E<T> { V(T, i64), N }
fn make() -> E<i64> { return N; }
fn f() -> i64 { let e: E<i64> = make(); return 1; }
",
        ),
        (
            "call-arg/qualified-unit",
            "module m;
enum E<T> { V(T, i64), N }
fn take(e: E<i64>) -> i64 { return 1; }
fn f() -> i64 { return take(E::N); }
",
        ),
        (
            "call-arg/bare-unit",
            "module m;
enum E<T> { V(T, i64), N }
fn take(e: E<i64>) -> i64 { return 1; }
fn f() -> i64 { return take(N); }
",
        ),
    ];
    for (name, src) in &shapes {
        assert_eq!(
            classify_fence(src),
            FenceVerdict::ByteEqual,
            "AG6-6: `{name}` is not byte-identical to the oracle. A generic-enum instance cell must              be sized 4 + max over ALL variants of the SUBSTITUTED payload widths. Under-allocating              is a silent memory bug; over-allocating breaks the byte capstones."
        );
    }
}

#[test]
fn ag6_7_unresolved_generic_enum_contexts_fail_closed() {
    let cases = [
        (
            "tuple element",
            "module m;
enum E<T> { V(T, i64), N }
fn f() -> i64 { let pair: (E<i64>, i64) = (E::N, 1); return 1; }
",
            FenceVerdict::Poison,
        ),
        (
            "record field",
            "module m;
enum E<T> { V(T, i64), N }
record Holder { value: E<i64> }
fn f() -> i64 { let h: Holder = Holder { value: E::N }; return 1; }
",
            FenceVerdict::Poison,
        ),
        (
            "method argument",
            "module m;
enum E<T> { V(T, i64), N }
record Holder { value: i64 }
impl Holder { fn take(self: Holder, e: E<i64>) -> i64 { return self::value; } }
fn f() -> i64 { let h: Holder = Holder { value: 1 }; return h.take(E::N); }
",
            FenceVerdict::Poison,
        ),
        (
            "qualified reassignment",
            "module m;
enum E<T> { V(T, i64), N }
fn f() -> i64 { let mut e: E<i64> = E::V(1, 2); e = E::N; return 1; }
",
            FenceVerdict::Poison,
        ),
        (
            "bare reassignment",
            "module m;
enum E<T> { V(T, i64), N }
fn f() -> i64 { let mut e: E<i64> = E::V(1, 2); e = N; return 1; }
",
            FenceVerdict::OracleRejects,
        ),
    ];
    for (name, src, expected) in cases {
        assert_eq!(
            classify_fence(src),
            expected,
            "AG6-7 `{name}`: a generic enum constructor without a resolved emitter context must fail closed"
        );
    }
}
