//! SH-RING — differential parity for the self-hosted ring-boundary checker.
//!
//! Composes `selfhost/lexer.sigil` + `parser.sigil` + `typecheck.sigil` +
//! `ring_check.sigil` into one tool emitting a `;`-joined R-code stream, compared as
//! a sorted-deduped SET against the authoritative Rust oracle `ring_check::check_rings`
//! run over the full pipeline (`parse → resolve → check_with_options → check_rings`,
//! oracle pinned 739784e). MIN_COVERED = {R001, R003}; R002 is DEMOTED (its only
//! trigger is also a T253 type error — ET-R1). The oracle MUST be called directly —
//! no parallel re-impl. See `docs/specs/sh-security-checkers.md`.

use sigil_compiler::CompileOptions;
use sigil_compiler::compile_tool;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{name_resolution, ring_check, type_check};
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");
const TYPECHECK: &str = include_str!("../../../selfhost/typecheck.sigil");
const RINGCHECK: &str = include_str!("../../../selfhost/ring_check.sigil");
const FUEL: u64 = 300_000_000;

/// The in-core R-code surface (R002 demoted — ET-R1). Both sides filter to this set
/// so the composed typecheck's T-codes can never pollute the comparison (ET-R7).
const CORE_R_CODES: &[&str] = &["R001", "R003"];

/// Strip the per-file `module X;` headers and concatenate into one `module tool;`.
fn rc_tool(body: &str) -> String {
    let lexer_defs = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser_defs = PARSER.replace("\nmodule parser;\n", "\n");
    let tc_defs = TYPECHECK.replace("\nmodule typecheck;\n", "\n");
    let rc_defs = RINGCHECK.replace("\nmodule ring_check;\n", "\n");
    format!(
        "module tool;\n{lexer_defs}\n{parser_defs}\n{tc_defs}\n{rc_defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// src -> lex -> parse -> rc_encode -> output.
fn rc_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = rc_encode(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

/// Compile the composed tool ONCE.
fn rc_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        compile_tool(&rc_tool(rc_body()))
            .expect("ring_check tool should compile")
            .wasm
    })
}

/// Full UTF-8 tool output for `src`.
fn full_output(src: &str) -> String {
    let result = execute_ephemeral(rc_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("ring_check tool executes");
    String::from_utf8(result.output).expect("tool output is UTF-8")
}

/// The self-hosted R-codes as a sorted-deduped set, filtered to CORE_R_CODES.
fn sigil_rcodes(src: &str) -> Vec<String> {
    let mut v: Vec<String> = full_output(src)
        .split(';')
        .filter(|s| !s.is_empty())
        .filter(|s| CORE_R_CODES.contains(s))
        .map(|s| s.to_string())
        .collect();
    v.sort();
    v.dedup();
    v
}

/// The oracle's R-codes as a sorted-deduped set, filtered to CORE_R_CODES. MUST call
/// the authoritative `ring_check::check_rings` over the real pipeline (ET-R7).
fn oracle_rcodes(src: &str) -> Vec<String> {
    let source = SourceFile::new("<rc-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    // ET-R7: the corpus is parse-clean. A parse-erroring fixture (e.g. a non-keyword
    // `struct`) would let the oracle "recover" by dropping items and pass vacuously
    // while the self-host parses it differently — a false parity. Reject it here.
    assert!(
        pdiags.is_empty(),
        "SH-RING fixture must be parse-clean (ET-R7): {src:?} -> {:?}",
        pdiags
            .iter()
            .map(|d| d.code().to_string())
            .collect::<Vec<_>>()
    );
    let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
    let (typed, _reg) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .expect("fixture must type-check (ET-R7: type-clean corpus)");
    let mut v: Vec<String> = match ring_check::check_rings(&typed) {
        Ok(_) => Vec::new(),
        Err(ds) => ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| CORE_R_CODES.contains(&c.as_str()))
            .collect(),
    };
    v.sort();
    v.dedup();
    v
}

// ─────────────────────────────────────────────────────────────────────────────
// Corpus (all type-clean — ET-R7; every oracle R-code arises from an in-core shape
// — ET-R4). Each fixture's expected deduped R-code set is pinned, and `oracle_rcodes`
// re-derives it from the live oracle so the pin and the oracle never drift (ET-R5).
// ─────────────────────────────────────────────────────────────────────────────

/// REJECT fixtures: (label, src, expected sorted-deduped R-set).
const CORPUS_REJECT: &[(&str, &str, &[&str])] = &[
    // R001 — an outer fn OWNING a cap param (the cleanest single-violation shape).
    (
        "R001 cap param (outer)",
        "#[ring(outer)] module m;\ncap type Fuel { burn }\nfn f(c: Fuel) -> i64 { return 0; }\n",
        &["R001"],
    ),
    // R001 — cap param AND cap return (the oracle emits two R001s → set {R001}).
    (
        "R001 cap param + return (outer)",
        "#[ring(outer)] module m;\ncap type Fuel { burn }\nfn f(c: Fuel) -> Fuel { return c; }\n",
        &["R001"],
    ),
    // R001 — a cap-typed body `let` (proves the outer-body let walk).
    (
        "R001 cap let (outer)",
        "#[ring(outer)] module m;\ncap type Fuel { burn }\nfn f(g: Fuel) -> Fuel {\n    let h: Fuel = g;\n    return h;\n}\n",
        &["R001"],
    ),
    // R003 — an inner fn body calling a declared extern (the R003.sigil shape).
    (
        "R003 inner extern call",
        "module ext;\nextern \"C\" fn foo() -> i64 ! { FFI, Unsafe };\nfn use_it() -> i64 {\n    return foo();\n}\n",
        &["R003"],
    ),
    // R003 — a `pub` (flags=4) module is STILL inner (ET-R3: ring = bit 0 only; pub
    // must not flip the ring). A `flags != 0` misread would skip R003 here.
    (
        "R003 pub-inner extern call (ET-R3 bit-0)",
        "pub module m;\nextern \"C\" fn foo() -> i64 ! { FFI, Unsafe };\nfn use_it() -> i64 {\n    return foo();\n}\n",
        &["R003"],
    ),
    // Multi-module: an outer module owning a cap (R001) + an inner module calling an
    // extern (R003) — proves per-module ring dispatch + the program-wide tables.
    (
        "multi-module R001 (outer) + R003 (inner)",
        "#[ring(outer)] module a;\ncap type Fuel { burn }\nfn f(c: Fuel) -> Fuel { return c; }\nmodule b;\nextern \"C\" fn foo() -> i64 ! { FFI, Unsafe };\nfn use_it() -> i64 {\n    return foo();\n}\n",
        &["R001", "R003"],
    ),
];

/// ACCEPT fixtures (CLEAN — no in-core R-code on either side).
const CORPUS_ACCEPT: &[(&str, &str)] = &[
    // ET-R2: a `&`-borrow param is the legitimate outer-ring grant path → NOT R001.
    (
        "R001 borrow param (outer) — clean (ET-R2)",
        "#[ring(outer)] module m;\ncap type Fuel { burn }\nfn f(c: &Fuel) -> i64 { return 0; }\n",
    ),
    // R001 is outer-only: an inner fn owning a cap is clean.
    (
        "inner cap-owning fn — clean (R001 is outer-only)",
        "module m;\ncap type Fuel { burn }\nfn f(c: Fuel) -> Fuel { return c; }\n",
    ),
    // R003 is inner-only: an outer (trusted) module calling an extern is clean.
    (
        "outer-trusted extern call — clean (R003 is inner-only)",
        "#[ring(outer)] #[trusted] module ext;\nextern \"C\" fn foo() -> i64 ! { FFI, Unsafe };\nfn use_it() -> i64 ! { FFI, Unsafe } {\n    return foo();\n}\n",
    ),
    // ET-R6: an extern NAMED but never CALLED in an inner body is clean.
    (
        "extern named-not-called (inner) — clean (ET-R6)",
        "module ext;\nextern \"C\" fn foo() -> i64 ! { FFI, Unsafe };\nfn use_it() -> i64 {\n    return 0;\n}\n",
    ),
    // An all-clean inner program.
    (
        "all-clean inner program",
        "module m;\nfn f() -> i64 { return 0; }\n",
    ),
    // ET-R3 clean twin: a pub (flags=4) inner module owning a cap is clean (pub does
    // not flip the ring → inner → no R001).
    (
        "pub-inner cap-owning — clean (ET-R3 / R001 outer-only)",
        "pub module m;\ncap type Fuel { burn }\nfn f(c: Fuel) -> Fuel { return c; }\n",
    ),
    // Multi-module all-clean (outer borrow + inner plain).
    (
        "multi-module all-clean (outer borrow + inner plain)",
        "#[ring(outer)] module a;\ncap type Fuel { burn }\nfn f(c: &Fuel) -> i64 { return 0; }\nmodule b;\nfn g() -> i64 { return 0; }\n",
    ),
    // AG-R8 regression: an UNCALLED generic fn owning a cap is CLEAN on both sides —
    // the oracle never monomorphizes it (no instance reaches check_rings), and the
    // self-host skips generic-source fns (rc_is_generic_fn). Without the skip the
    // self-host false-fired R001 here (found by the adversarial sweep).
    (
        "uncalled generic cap fn (outer) — clean (AG-R8 generic-skip)",
        "#[ring(outer)] module m;\ncap type Fuel { burn }\nfn helper<T>(c: Fuel, x: T) -> T { return x; }\nfn real() -> i64 { return 0; }\n",
    ),
    // AG-R8 R003 twin: an UNCALLED generic fn in an inner module calling an extern is
    // clean on both sides (no instance for the oracle; generic-skip for the self-host).
    (
        "uncalled generic extern-calling fn (inner) — clean (AG-R8)",
        "module ext;\nextern \"C\" fn foo() -> i64 ! { FFI, Unsafe };\nfn use_it<T>(x: T) -> i64 { return foo(); }\nfn real() -> i64 { return 0; }\n",
    ),
];

/// DONE-LINE GATE (reject half): every reject fixture reproduces the oracle's R-code
/// set exactly, AND that set equals the pinned expectation (so the pin can never
/// silently drift from the oracle).
#[test]
fn sh_ring_reject_matches_oracle() {
    for (label, src, expected) in CORPUS_REJECT {
        let oracle = oracle_rcodes(src);
        let exp: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        assert_eq!(
            oracle, exp,
            "SH-RING {label}: the oracle must emit the pinned R-set:\n{src}"
        );
        assert_eq!(
            sigil_rcodes(src),
            oracle,
            "SH-RING {label}: self-hosted R-codes must match the oracle:\n{src}"
        );
    }
}

/// DONE-LINE GATE (accept half): every accept fixture is CLEAN on both sides (0
/// in-core R-codes) — the no-false-positive / soundness floor (ET-R5: sigil_R ⊆
/// oracle_R, here both empty).
#[test]
fn sh_ring_accept_is_clean_both_sides() {
    for (label, src) in CORPUS_ACCEPT {
        assert!(
            oracle_rcodes(src).is_empty(),
            "SH-RING {label}: the accept fixture must be ring-clean in the oracle:\n{src}"
        );
        assert!(
            sigil_rcodes(src).is_empty(),
            "SH-RING {label}: self-hosted emitted a spurious R-code on a clean fixture:\n{src}"
        );
    }
}

/// SOUNDNESS SUBSET (ET-R5): on EVERY fixture (reject ∪ accept), the self-hosted
/// R-set is a SUBSET of the oracle's — never a false R-code (which would reject valid
/// code). On the in-core corpus the two gates above also assert exact equality.
#[test]
fn sh_ring_no_false_rcode_subset() {
    let all = CORPUS_REJECT
        .iter()
        .map(|(l, s, _)| (*l, *s))
        .chain(CORPUS_ACCEPT.iter().copied());
    for (label, src) in all {
        let oracle = oracle_rcodes(src);
        for code in sigil_rcodes(src) {
            assert!(
                oracle.contains(&code),
                "SH-RING {label}: self-hosted emitted {code} not in the oracle set {oracle:?}:\n{src}"
            );
        }
    }
}

/// NON-STUB: a REAL R001 and a REAL R003 each fire on both sides, and >=2 distinct
/// full streams exist (a stub that emits "" everywhere, or a constant, fails here).
#[test]
fn sh_ring_non_stub() {
    let r001 =
        "#[ring(outer)] module m;\ncap type Fuel { burn }\nfn f(c: Fuel) -> i64 { return 0; }\n";
    let r003 = "module ext;\nextern \"C\" fn foo() -> i64 ! { FFI, Unsafe };\nfn use_it() -> i64 {\n    return foo();\n}\n";
    assert_eq!(
        sigil_rcodes(r001),
        vec!["R001".to_string()],
        "R001 must fire"
    );
    assert_eq!(oracle_rcodes(r001), vec!["R001".to_string()], "R001 oracle");
    assert_eq!(
        sigil_rcodes(r003),
        vec!["R003".to_string()],
        "R003 must fire"
    );
    assert_eq!(oracle_rcodes(r003), vec!["R003".to_string()], "R003 oracle");

    let mut streams: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (_, src, _) in CORPUS_REJECT {
        streams.insert(full_output(src));
    }
    for (_, src) in CORPUS_ACCEPT {
        streams.insert(full_output(src));
    }
    assert!(
        streams.len() >= 2,
        "stub: all fixtures produced identical streams"
    );
}

/// DETERMINISM (ET-R7): two runs of the compiled tool are byte-identical.
#[test]
fn sh_ring_deterministic() {
    let all = CORPUS_REJECT
        .iter()
        .map(|(_, s, _)| *s)
        .chain(CORPUS_ACCEPT.iter().map(|(_, s)| *s));
    for src in all {
        assert_eq!(
            full_output(src),
            full_output(src),
            "non-deterministic: {src}"
        );
    }
}
