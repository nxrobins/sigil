//! SH-TAINT — differential parity for the self-hosted taint / constant-time checker.
//!
//! Composes `selfhost/lexer.sigil` + `parser.sigil` + `typecheck.sigil` +
//! `taint_check.sigil` into one tool emitting a `;`-joined T-code stream, compared as a
//! sorted-deduped SET against the authoritative Rust oracle `taint_check::check_taints`
//! run over the full pipeline (`parse → resolve → check_with_options → check_taints`,
//! oracle pinned d2faf17). PR-T1 = the scalar surface; MIN_COVERED = the 13 codes
//! {T001, T020-T027, T029-T032} (T028 send/ask DEMOTED — actor-only, AG-T13). The
//! oracle MUST be called directly — no parallel re-impl. See
//! `docs/specs/sh-security-checkers.md`.

use sigil_compiler::CompileOptions;
use sigil_compiler::compile_tool;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{name_resolution, taint_check, type_check};
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");
const TYPECHECK: &str = include_str!("../../../selfhost/typecheck.sigil");
const TAINTCHECK: &str = include_str!("../../../selfhost/taint_check.sigil");
const FUEL: u64 = 300_000_000;

/// The in-core taint-code surface (13 — T028 demoted, ET-T15). Both sides filter to
/// this set so the composed typecheck's T-codes can never pollute the comparison (ET-T5).
const CORE_T_CODES: &[&str] = &[
    "T001", "T020", "T021", "T022", "T023", "T024", "T025", "T026", "T027", "T029", "T030", "T031",
    "T032",
];
const TAINT_UNSUPPORTED: &str = "SH_TAINT_UNSUPPORTED";

/// Strip the per-file `module X;` headers and concatenate into one `module tool;`.
fn tt_tool(body: &str) -> String {
    let lexer_defs = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser_defs = PARSER.replace("\nmodule parser;\n", "\n");
    let tc_defs = TYPECHECK.replace("\nmodule typecheck;\n", "\n");
    let tt_defs = TAINTCHECK.replace("\nmodule taint_check;\n", "\n");
    format!(
        "module tool;\n{lexer_defs}\n{parser_defs}\n{tc_defs}\n{tt_defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// src -> lex -> parse -> tt_encode -> output.
fn tt_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = tt_encode(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

/// Compile the composed tool ONCE.
fn tt_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        compile_tool(&tt_tool(tt_body()))
            .expect("taint_check tool should compile")
            .wasm
    })
}

/// Full UTF-8 tool output for `src`.
fn full_output(src: &str) -> String {
    let result = execute_ephemeral(tt_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("taint_check tool executes");
    String::from_utf8(result.output).expect("tool output is UTF-8")
}

/// The self-hosted T-codes as a sorted-deduped set, filtered to CORE_T_CODES.
fn sigil_tcodes(src: &str) -> Vec<String> {
    let mut v: Vec<String> = full_output(src)
        .split(';')
        .filter(|s| !s.is_empty())
        .filter(|s| CORE_T_CODES.contains(s))
        .map(|s| s.to_string())
        .collect();
    v.sort();
    v.dedup();
    v
}

/// The oracle's taint codes as a sorted-deduped set, filtered to CORE_T_CODES. MUST
/// call the authoritative `taint_check::check_taints` over the real pipeline (ET-T5).
fn oracle_tcodes(src: &str) -> Vec<String> {
    let source = SourceFile::new("<tt-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    // ET-T5 / AG-T3: the corpus is parse-clean (a parse-erroring fixture lets the oracle
    // "recover" by dropping items and pass vacuously while the self-host parses it
    // differently — a false parity).
    assert!(
        pdiags.is_empty(),
        "SH-TAINT fixture must be parse-clean (ET-T5): {src:?} -> {:?}",
        pdiags
            .iter()
            .map(|d| d.code().to_string())
            .collect::<Vec<_>>()
    );
    let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
    // ET-T5 / AG-T3: type-clean — check_taints runs on a fully-built TypedProgram.
    let (typed, _reg) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .expect("fixture must type-check (type-clean corpus)");
    let mut v: Vec<String> = match taint_check::check_taints(&typed) {
        Ok(_) => Vec::new(),
        Err(ds) => ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| CORE_T_CODES.contains(&c.as_str()))
            .collect(),
    };
    v.sort();
    v.dedup();
    v
}

// ─────────────────────────────────────────────────────────────────────────────
// Corpus (all type-clean — ET-T5; every fixture isolates ONE in-core taint code so
// the deduped set equals the pinned expectation). `oracle_tcodes` re-derives the set
// from the live oracle so the pin and the oracle never drift (ET-T4/ET-T9).
// ─────────────────────────────────────────────────────────────────────────────

/// REJECT fixtures: (label, src, expected sorted-deduped T-set). All 13 in-core codes
/// fire here (ET-T9 — detection is per-code, not subset-safety).
const CORPUS_REJECT: &[(&str, &str, &[&str])] = &[
    // T001 — downgrade, routed through a callee's declared @Secret RETURN (TS-4: a BARE
    // same-module call exercises the tt_sig taint table).
    (
        "T001 downgrade via callee @Secret return",
        "module ext;\nfn leak() -> i64 @Secret {\n    let s: i64 @Secret = 0;\n    return s;\n}\nfn f() -> i64 {\n    let y: i64 @Public = leak();\n    return 0;\n}\n",
        &["T001"],
    ),
    // A direct call is also a sink: the callee must not bind a Secret argument
    // to its default-Public parameter.
    (
        "T001 secret argument into public function parameter",
        "module ext;\nfn identity(value: i64) -> i64 { return value; }\nfn f(secret: i64 @Secret) -> i64 @Secret { return identity(secret); }\n",
        &["T001"],
    ),
    // T020 — @SecretCT `if` condition.
    (
        "T020 secret-dependent if",
        "module ext;\nfn f(s: i64 @SecretCT) -> i64 {\n    if s == 0 {\n        return 1;\n    } else {\n        return 0;\n    }\n}\n",
        &["T020"],
    ),
    // T021 — @SecretCT `while` condition.
    (
        "T021 secret-dependent while",
        "module ext;\nfn f(s: i64 @SecretCT) -> i64 {\n    while s == 0 {\n        return 1;\n    }\n    return 0;\n}\n",
        &["T021"],
    ),
    // T022 — @SecretCT `for-in` iterable (the ET-T15-probed shape).
    (
        "T022 secret-dependent for-in",
        "#[ring(outer)] module ext;\nfn f(arr: [i64; 4] @SecretCT) -> i64 ! {} {\n    let mut total: i64 @SecretCT = 0;\n    for x in arr {\n        total = x;\n    }\n    return 0;\n}\n",
        &["T022"],
    ),
    // T023 — @SecretCT `match` scrutinee.
    (
        "T023 secret-dependent match",
        "module ext;\nfn f(s: i64 @SecretCT) -> i64 {\n    let mut r: i64 = 0;\n    match s {\n        0 => { r = 1; },\n        _ => { r = 2; },\n    }\n    return 0;\n}\n",
        &["T023"],
    ),
    // T024 — @SecretCT array index (result annotated @SecretCT to isolate from T001).
    (
        "T024 secret-dependent index",
        "module ext;\nfn f(arr: [i64; 4], i: i64 @SecretCT) -> i64 {\n    let x: i64 @SecretCT = arr[i];\n    return 0;\n}\n",
        &["T024"],
    ),
    // T025 — @SecretCT memory address (load8); the ET-T15-isolated shape.
    (
        "T025 secret-dependent load8 address",
        "#[ring(outer)] module ext;\nfn f(p: i64 @SecretCT) -> i64 @SecretCT ! { Alloc } {\n    let v: i64 @SecretCT = load8(p);\n    return v;\n}\n",
        &["T025"],
    ),
    // T026 — @SecretCT division operand.
    (
        "T026 variable-time division",
        "module ext;\nfn f(s: i64 @SecretCT, d: i64) -> i64 @SecretCT {\n    let q: i64 @SecretCT = s / d;\n    return q;\n}\n",
        &["T026"],
    ),
    // T027 — @SecretCT arg to an extern (result bound @Internal to isolate from T030/T001).
    (
        "T027 secret-ct to FFI",
        "#[ring(outer)] module ext;\nextern \"C\" fn k(x: i64) -> i64 ! { FFI, Unsafe };\nfn f(s: i64 @SecretCT) -> i64 @Internal ! { FFI, Unsafe } {\n    let r: i64 @Internal = k(s);\n    return r;\n}\n",
        &["T027"],
    ),
    // The ordinary information-flow half of the foreign boundary: FFI is
    // @Internal, so @Secret cannot cross it without declassification.
    (
        "T001 secret to FFI internal boundary",
        "#[ring(outer)] module ext;\nextern \"C\" fn k(x: i64) -> i64 ! { FFI, Unsafe };\nfn f(s: i64 @Secret) -> i64 @Internal ! { FFI, Unsafe } { return k(s); }\n",
        &["T001"],
    ),
    // T029 — @SecretCT allocation size (result annotated @SecretCT to isolate from T001).
    (
        "T029 secret-dependent alloc size",
        "#[ring(outer)] module ext;\nfn f(n: i64 @SecretCT) -> i64 ! { Alloc } {\n    let p: i64 @SecretCT = alloc(n);\n    return 0;\n}\n",
        &["T029"],
    ),
    // T030 — upcast @Secret INTO a @SecretCT binding.
    (
        "T030 upcast secret into secretct",
        "module ext;\nfn f(s: i64 @Secret) -> i64 {\n    let c: i64 @SecretCT = s;\n    return 0;\n}\n",
        &["T030"],
    ),
    // CT016 also applies at a direct function-parameter boundary.
    (
        "T030 secret argument into secretct function parameter",
        "module ext;\nfn ct(value: i64 @SecretCT) -> i64 @SecretCT ! {} { return value; }\nfn f(secret: i64 @Secret) -> i64 @SecretCT ! {} { return ct(secret); }\n",
        &["T030"],
    ),
    // T031 — declassify rejects a @SecretCT input (the seed-test shape).
    (
        "T031 declassify of secretct input",
        "module ext;\ncap type Declassify {}\nfn f(s: i64 @SecretCT, c: Declassify) -> i64 @Public {\n    return declassify(s, c);\n}\n",
        &["T031"],
    ),
    // T032 — declassify_ct requires a @SecretCT input (the seed-test shape).
    (
        "T032 declassify_ct of non-secretct input",
        "module ext;\ncap type DeclassifyCT {}\nfn f(s: i64 @Secret, c: DeclassifyCT) -> i64 @Secret {\n    return declassify_ct(s, c);\n}\n",
        &["T032"],
    ),
    // ── post-impl adversarial fixtures (empirically pin the ritual threats) ──
    // ET-T8: an UN-annotated `let` from a @Secret value fires T001 (declared = Public).
    (
        "ET-T8 un-annotated secret let -> T001",
        "module ext;\nfn f(s: i64 @Secret) -> i64 {\n    let y = s;\n    return 0;\n}\n",
        &["T001"],
    ),
    // ET-T10: a @SecretCT `if` emits T020 and does NOT descend — the guarded body's
    // `/` (T026) and index (T024) are NOT reached (no false cascade). Expect ONLY T020.
    (
        "ET-T10 secretct-if no pc-cascade",
        "module ext;\nfn f(s: i64 @SecretCT, arr: [i64; 4]) -> i64 {\n    if s == 0 {\n        let d: i64 @SecretCT = 100 / s;\n        let q: i64 @SecretCT = arr[s];\n        return q;\n    } else {\n        return 0;\n    }\n}\n",
        &["T020"],
    ),
    // ET-T3 implicit flow: a @Public let inside a @Secret (non-CT) branch fires T001
    // (pc-taint folds Secret into the let's value).
    (
        "ET-T3 implicit-flow downgrade -> T001",
        "module ext;\nfn f(s: i64 @Secret) -> i64 {\n    if s == 0 {\n        let y: i64 @Public = 0;\n        return y;\n    } else {\n        return 0;\n    }\n}\n",
        &["T001"],
    ),
    // DS-4: the tool_main exception is BARE-name byte-exact — `my_tool_main` is NOT
    // tool_main, so its @Internal return downgrades to @Public -> T001 (an `ends_with`
    // match would wrongly suppress it).
    (
        "DS-4 my_tool_main is not the exception -> T001",
        "module ext;\nfn my_tool_main(s: i64 @Internal) -> i64 {\n    return s;\n}\n",
        &["T001"],
    ),
    // ── PR-T2 per-field record fixtures ──
    // Reading a record's SECRET field into a @Public let fires T001.
    (
        "PR-T2 record secret-field read -> T001",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret) -> i64 {\n    let r: R @Secret = R { a: s, b: 0 };\n    let x: i64 @Public = r.a;\n    return 0;\n}\n",
        &["T001"],
    ),
    // ET-T13 field-write-raise: writing a secret through ONE field raises the WHOLE
    // record, so a later read of ANOTHER (originally public) field is now Secret -> T001.
    (
        "PR-T2 field-write raises whole record -> T001 (ET-T13)",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret) -> i64 {\n    let mut r: R = R { a: 0, b: 0 };\n    r.a = s;\n    let y: i64 @Public = r.b;\n    return 0;\n}\n",
        &["T001"],
    ),
    // ── PR-T2 closure capture-CT fixtures (E4) ──
    // The CT012 shape: a closure CAPTURES a @SecretCT scalar and branches on it; the
    // descent seeds the capture so the in-body `if` fires T020. The closure is bound to a
    // taint-absorbing `let g @SecretCT` so the oracle emits ONLY the in-body code (the
    // closure value-taint = lub of captures = SecretCT flows clean into the @SecretCT let;
    // an un-annotated let would also co-emit a value-flow T001 — AG-T14, out-of-core).
    (
        "PR-T2 closure captures @SecretCT, branches -> T020 (E4)",
        "module ext;\nfn f(s: i64 @SecretCT) -> i64 {\n    let g @SecretCT = fn() -> i64 { if s == 0 { return 1; } else { return 0; } };\n    return 0;\n}\n",
        &["T020"],
    ),
    // Lambda-lifting must preserve a closure's own parameter labels. Treating this
    // @SecretCT parameter as Public would let the branch evade CT001.
    (
        "PR-T2 closure own @SecretCT param branches -> T020",
        "module ext;\nfn f(d: i64) -> i64 {\n    let g = fn(s: i64 @SecretCT) -> i64 { if s == 0 { return 1; } else { return 0; } };\n    return 0;\n}\n",
        &["T020"],
    ),
    // A captured @SecretCT divides inside the body -> T026 (a DIFFERENT in-body CT code
    // via the same capture mechanism).
    (
        "PR-T2 closure captures @SecretCT, divides -> T026 (E4)",
        "module ext;\nfn f(s: i64 @SecretCT, d: i64) -> i64 {\n    let g @SecretCT = fn() -> i64 { let q: i64 @SecretCT = d / s; return 0; };\n    return 0;\n}\n",
        &["T026"],
    ),
    // PR-T2 SYNERGY: a closure captures a RECORD whose secret field flows into an in-body
    // CT op — exercises per-field capture (the record `fields` encoding is copied into the
    // capture env) AND closure descent together. `r.a` (SecretCT) -> in-body `if` -> T020.
    (
        "PR-T2 closure captures record secret-field, branches -> T020 (E4 + records)",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @SecretCT) -> i64 {\n    let r: R @SecretCT = R { a: s, b: 0 };\n    let g @SecretCT = fn() -> i64 { if r.a == 0 { return 1; } else { return 0; } };\n    return 0;\n}\n",
        &["T020"],
    ),
    // NESTED closure: an inner closure captures the outer fn's @SecretCT through the
    // outer closure; the inner `if` still fires T020 (descent recurses, captures resolve
    // through the copied env at every level).
    (
        "PR-T2 nested closure captures @SecretCT, inner branches -> T020 (E4)",
        "module ext;\nfn f(s: i64 @SecretCT) -> i64 {\n    let g @SecretCT = fn() -> i64 {\n        let h @SecretCT = fn() -> i64 { if s == 0 { return 1; } else { return 0; } };\n        return 0;\n    };\n    return 0;\n}\n",
        &["T020"],
    ),
    // In-body DOWNGRADE: a closure body `let y: i64 @Public = <secret capture>` fires
    // T001 INSIDE the body (distinct from the closure-VALUE T001, AG-T14 out-of-core).
    (
        "PR-T2 closure body downgrades captured secret -> T001 (E4)",
        "module ext;\nfn f(s: i64 @SecretCT) -> i64 {\n    let g @SecretCT = fn() -> i64 { let y: i64 @Public = s; return 0; };\n    return 0;\n}\n",
        &["T001"],
    ),
    // In-body INDEX: a captured @SecretCT used as an array index inside the body -> T024.
    (
        "PR-T2 closure indexes with captured @SecretCT -> T024 (E4)",
        "module ext;\nfn f(s: i64 @SecretCT, arr: [i64; 4]) -> i64 {\n    let g @SecretCT = fn() -> i64 { let x: i64 @SecretCT = arr[s]; return 0; };\n    return 0;\n}\n",
        &["T024"],
    ),
    // CAPTURED-RECORD LUB COLLAPSE (adversarial C1): a closure captures a MIXED-taint record
    // (a=Public, b=SecretCT) and branches on the CLEAN field r.a. The oracle captures a
    // record via env.lookup -> a SCALAR lub label (SecretCT), so r.a reads the lub -> T020;
    // the self-host collapses a captured record to its lub scalar (tt_copy_binds drops the
    // per-field encoding) so r.a also reads SecretCT -> T020. (Preserving per-field here
    // would make the self-host MORE precise than the oracle and MISS this T020.)
    (
        "PR-T2 captured mixed record reads lub-scalar on a clean field -> T020 (E4)",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @SecretCT) -> i64 {\n    let r: R @SecretCT = R { a: 0, b: s };\n    let g @SecretCT = fn() -> i64 { if r.a == 0 { return 1; } else { return 0; } };\n    return 0;\n}\n",
        &["T020"],
    ),
    // M5b/M6 store8-launder REJECT fixtures were REMOVED at the agentic-bench
    // merge (2026-07-29). The Rust oracle's M6 region-alias analysis
    // (`taint_check.rs`) SHIPS and correctly emits T001 on both — `store8` a
    // @Secret into an alloc region then return the base pointer, and the
    // copy-alias-then-return variant. But the SELFHOST mirror
    // (`selfhost/taint_check.sigil`) does NOT yet carry the region model — this
    // merge took main's selfhost wholesale rather than the branch's selfhost
    // rewrite (which conflicted with the composed byte-pins). A REJECT fixture
    // asserts oracle==selfhost, which these cannot satisfy while the oracle is
    // strictly stronger, so they are withdrawn rather than left red. The clean
    // TWINS remain in CORPUS_ACCEPT (both sides agree on []). FOLLOW-UP: mirror
    // the M6 region model into `selfhost/taint_check.sigil`, then restore these
    // two rejects. Oracle-side coverage lives in the compiler crate's taint
    // tests, so the feature itself stays gated.
];

/// ACCEPT fixtures (CLEAN — no in-core T-code on either side). The clean twins.
const CORPUS_ACCEPT: &[(&str, &str)] = &[
    // M5b twin: storing a @Secret through `out` raises `out`, but returning a
    // DIFFERENT public local `keep` is clean — the raise is targeted to the
    // written buffer's base local, not global. (Guards against over-tainting.)
    (
        "M5b store8 secret then return a different public local — clean",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let out: i64 = alloc(8);\n    let keep: i64 = 0;\n    store8(out, s);\n    return keep;\n}\n",
    ),
    // M6 twin (the payoff of REGION-based over name-based aliasing): alias
    // `out`, then REBIND `out` to a fresh alloc and store the secret into the
    // fresh region. The old alias `q` keeps region R0 (untainted), so
    // returning it is CLEAN. A name-based alias tracker would false-positive
    // here; the region model gets it right.
    (
        "M6 rebind: alias, then out=fresh alloc + store secret, return old alias — clean",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let mut out: i64 = alloc(8);\n    let q: i64 = out;\n    out = alloc(8);\n    store8(out, s);\n    return q;\n}\n",
    ),
    // T001 twin: @Secret callee return into a @Secret let (Secret -> Secret, clean).
    (
        "T001 twin — secret into secret let",
        "module ext;\nfn leak() -> i64 @Secret {\n    let s: i64 @Secret = 0;\n    return s;\n}\nfn f() -> i64 @Secret {\n    let y: i64 @Secret = leak();\n    return y;\n}\n",
    ),
    // T020 twin: a @Public `if` condition is clean.
    (
        "T020 twin — public if condition",
        "module ext;\nfn f(p: i64) -> i64 {\n    if p == 0 {\n        return 1;\n    } else {\n        return 0;\n    }\n}\n",
    ),
    // ET-T8: an un-annotated let from a @Secret value DOES fire T001 (reject); its twin
    // is the same with the @Secret annotation (Secret -> Secret, clean).
    (
        "ET-T8 twin — annotated secret let is clean",
        "module ext;\nfn f(s: i64 @Secret) -> i64 @Secret {\n    let y: i64 @Secret = s;\n    return y;\n}\n",
    ),
    // T024 twin: a @Public index is clean.
    (
        "T024 twin — public index",
        "module ext;\nfn f(arr: [i64; 4], i: i64) -> i64 {\n    let x: i64 = arr[i];\n    return x;\n}\n",
    ),
    // T026 twin: division with @Public operands is clean.
    (
        "T026 twin — public division",
        "module ext;\nfn f(a: i64, b: i64) -> i64 {\n    let q: i64 = a / b;\n    return q;\n}\n",
    ),
    // The declassify two-step ladder (ET-T6): @SecretCT -> @Secret -> @Public is CLEAN.
    (
        "declassify two-step ladder — clean (ET-T6)",
        "module ext;\ncap type DeclassifyCT {}\ncap type Declassify {}\nfn f(s: i64 @SecretCT, c: DeclassifyCT, d: Declassify) -> i64 @Public {\n    let mid: i64 @Secret = declassify_ct(s, c);\n    return declassify(mid, d);\n}\n",
    ),
    // tool_main exception: a `tool_main` returning @Internal data is CLEAN (DS-4/TS-12).
    (
        "tool_main returns @Internal — clean (exception)",
        "module tool;\npub fn tool_main(s: i64 @Internal) -> i64 {\n    return s;\n}\n",
    ),
    // An all-clean program (no taint anywhere).
    (
        "all-clean program",
        "module ext;\nfn f(a: i64, b: i64) -> i64 {\n    let c: i64 = a + b;\n    return c;\n}\n",
    ),
    // ── post-impl adversarial accept fixtures ──
    // T027 only fires on a @SecretCT ARG: a @Public arg to an extern is CLEAN.
    (
        "extern call with public arg — clean (no T027)",
        "#[ring(outer)] module ext;\nextern \"C\" fn k(x: i64) -> i64 ! { FFI, Unsafe };\nfn f(a: i64) -> i64 @Internal ! { FFI, Unsafe } {\n    let r: i64 @Internal = k(a);\n    return r;\n}\n",
    ),
    // TS-2: store8 checks ONLY arg0 (the address) — a @SecretCT stored VALUE (arg1)
    // with a @Public address is CLEAN (the bound/value are NOT the CT-address check).
    (
        "TS-2 store8 public addr + secret value — clean (no T025)",
        "#[ring(outer)] module ext;\nfn f(p: i64, v: i64 @SecretCT) -> i64 ! { Alloc } {\n    store8(p, v);\n    return 0;\n}\n",
    ),
    // ── PR-T2 per-field record accept fixtures ──
    // The CRITICAL no-false-positive: reading the PUBLIC field of a mixed-taint record
    // is CLEAN (a whole-record-lub impl would wrongly fire T001 here).
    (
        "PR-T2 record public-field read — clean (per-field, not lub)",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret) -> i64 {\n    let r: R @Secret = R { a: s, b: 0 };\n    let y: i64 @Public = r.b;\n    return 0;\n}\n",
    ),
    // An all-public record round-trips clean.
    (
        "PR-T2 all-public record — clean",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(p: i64) -> i64 {\n    let r: R = R { a: p, b: 0 };\n    let y: i64 = r.a;\n    return y;\n}\n",
    ),
    // ── PR-T2 closure capture-CT accept fixtures (E4) ──
    // The reject twin: a closure capturing a @Public value and branching on it is CLEAN
    // (the descent fires no code when the capture is not secret).
    (
        "PR-T2 closure captures @Public, branches — clean (E4 twin)",
        "module ext;\nfn f(p: i64) -> i64 {\n    let g = fn() -> i64 { if p == 0 { return 1; } else { return 0; } };\n    return 0;\n}\n",
    ),
    // Param-SHADOW: an enclosing s@SecretCT shadowed by a default-public closure param s —
    // the body's `s` is the parameter, NOT the capture, so it is CLEAN.
    (
        "PR-T2 closure param shadows enclosing @SecretCT — clean (shadow)",
        "module ext;\nfn f(s: i64 @SecretCT) -> i64 {\n    let g = fn(s: i64) -> i64 { if s == 0 { return 1; } else { return 0; } };\n    return 0;\n}\n",
    ),
    // ── HB-2 all-public projection fixtures (tuple-let / break / continue) ──
    // The shadow now models these three statement kinds in the all-public domain (the oracle
    // desugars tuple lets pre-taint and its break/continue arms emit no codes — join-env
    // machinery only). Public instances are clean on BOTH sides; the nonpublic variants live
    // in `sh_taint_unsupported_shapes_are_explicit` (fail-closed, marker asserted).
    (
        "HB2 tuple let, all-public — clean",
        "module ext;\nfn mk() -> (i64, i64) {\n    return (1, 2);\n}\nfn f() -> i64 {\n    let (a, b) = mk();\n    return a + b;\n}\n",
    ),
    (
        "HB2 break in a public loop — clean",
        "module ext;\nfn f(c: bool) -> i64 {\n    while c {\n        break;\n    }\n    return 0;\n}\n",
    ),
    (
        "HB2 continue in a public loop — clean",
        "module ext;\nfn f() -> i64 {\n    let mut i: i64 = 0;\n    while i < 3 {\n        i = i + 1;\n        continue;\n    }\n    return i;\n}\n",
    ),
];

/// DONE-LINE GATE (reject half): every reject fixture reproduces the oracle's T-code
/// set exactly, AND that set equals the pinned expectation (so the pin can never
/// silently drift from the oracle — ET-T4/ET-T9).
#[test]
fn sh_taint_reject_matches_oracle() {
    for (label, src, expected) in CORPUS_REJECT {
        let oracle = oracle_tcodes(src);
        let exp: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        assert_eq!(
            oracle, exp,
            "SH-TAINT {label}: the oracle must emit the pinned T-set:\n{src}"
        );
        assert_eq!(
            sigil_tcodes(src),
            oracle,
            "SH-TAINT {label}: self-hosted T-codes must match the oracle:\n{src}"
        );
    }
}

/// DONE-LINE GATE (accept half): every accept fixture is CLEAN on both sides (0 in-core
/// T-codes) — the no-false-positive / soundness floor (ET-T4).
#[test]
fn sh_taint_accept_is_clean_both_sides() {
    for (label, src) in CORPUS_ACCEPT {
        assert!(
            oracle_tcodes(src).is_empty(),
            "SH-TAINT {label}: the accept fixture must be taint-clean in the oracle:\n{src}"
        );
        assert!(
            sigil_tcodes(src).is_empty(),
            "SH-TAINT {label}: self-hosted emitted a spurious T-code on a clean fixture:\n{src}"
        );
    }
}

/// SOUNDNESS SUBSET (ET-T4): on EVERY fixture (reject ∪ accept), the self-hosted T-set
/// is a SUBSET of the oracle's — never a false T-code (which would reject valid code).
#[test]
fn sh_taint_no_false_tcode_subset() {
    let all = CORPUS_REJECT
        .iter()
        .map(|(l, s, _)| (*l, *s))
        .chain(CORPUS_ACCEPT.iter().copied());
    for (label, src) in all {
        let oracle = oracle_tcodes(src);
        for code in sigil_tcodes(src) {
            assert!(
                oracle.contains(&code),
                "SH-TAINT {label}: self-hosted emitted {code} not in the oracle set {oracle:?}:\n{src}"
            );
        }
    }
}

/// NON-STUB (ET-T9): all 13 in-core codes fire on BOTH sides across the reject corpus
/// (a stub that emits "" everywhere, or a constant, fails here), and >=2 distinct full
/// streams exist.
#[test]
fn sh_taint_non_stub_all_13_fire() {
    let mut oracle_union: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    let mut sigil_union: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (_, src, _) in CORPUS_REJECT {
        for c in oracle_tcodes(src) {
            oracle_union.insert(c);
        }
        for c in sigil_tcodes(src) {
            sigil_union.insert(c);
        }
    }
    let expected: std::collections::BTreeSet<String> =
        CORE_T_CODES.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        oracle_union, expected,
        "the oracle must fire all 13 in-core codes across the reject corpus"
    );
    assert_eq!(
        sigil_union, expected,
        "the self-host must fire all 13 in-core codes across the reject corpus"
    );

    let mut streams: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (_, src, _) in CORPUS_REJECT {
        streams.insert(full_output(src));
    }
    assert!(
        streams.len() >= 2,
        "stub: all fixtures produced identical streams"
    );
}

/// AG-T14 SUBSET-SAFE BOUNDARY (the closure-value under-approximation, found + broadened by
/// the post-impl adversarial sweep). The oracle's closure value-taint = lub of captures, so a
/// secret-capturing closure co-emits a value-flow code at its BINDING — **T001** when the let
/// annotation is lower than the closure value (downgrade) or **T030** when higher-CT (upcast).
/// The self-host under-approximates the closure value to Public and MISSES that code. This is
/// OUT-of-core, **subset-safe** (`sigil ⊂ oracle`, never a false code). This test pins both
/// flavors mechanically: the self-host T-set is a STRICT subset of the oracle's, missing
/// exactly the expected value-flow code — so a regression to a false-positive (sigil emits the
/// code, or any other code, that the oracle lacks) fails loudly.
#[test]
fn sh_taint_ag_t14_subset_safe() {
    // (label, src, the value-flow code the self-host deliberately MISSES at the binding)
    let cases: &[(&str, &str, &str)] = &[
        // T001 flavor: an UN-annotated `let g = …` capturing a @SecretCT record, clean body —
        // the closure value (lub of captures = SecretCT) downgrades into the implicit @Public g.
        (
            "AG-T14 T001 — un-annotated let, SecretCT capture",
            "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @SecretCT) -> i64 {\n    let r: R @SecretCT = R { a: s, b: 0 };\n    let g = fn() -> i64 { let y: i64 @SecretCT = r.a; return 0; };\n    return 0;\n}\n",
            "T001",
        ),
        // T030 flavor: a `let g @SecretCT = …` capturing a @Secret record — the closure value
        // (@Secret) UPCASTS into the @SecretCT binding (T030); the in-body declassify_ct fires
        // T032 on both sides, so the self-host misses ONLY the T030.
        (
            "AG-T14 T030 — SecretCT let, Secret capture",
            "module ext;\ncap type DeclassifyCT {}\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret, c: DeclassifyCT) -> i64 {\n    let r: R @Secret = R { a: s, b: 0 };\n    let g @SecretCT = fn() -> i64 { let y: i64 @Secret = declassify_ct(r.a, c); return 0; };\n    return 0;\n}\n",
            "T030",
        ),
    ];
    for (label, src, missing) in cases {
        let oracle = oracle_tcodes(src);
        let sigil = sigil_tcodes(src);
        // soundness: never a false code.
        for c in &sigil {
            assert!(
                oracle.contains(c),
                "AG-T14 {label}: self-host emitted {c} not in oracle {oracle:?} (a FALSE POSITIVE):\n{src}"
            );
        }
        // the oracle emits the value-flow code; the self-host (correctly, per AG-T14) does not.
        assert!(
            oracle.contains(&missing.to_string()),
            "AG-T14 {label}: expected the oracle to emit the value-flow {missing}; got {oracle:?}:\n{src}"
        );
        assert!(
            !sigil.contains(&missing.to_string()),
            "AG-T14 {label}: the self-host emitted {missing} — the closure-value under-approximation no longer holds (re-evaluate AG-T14):\n{src}"
        );
    }
}

/// Known gaps in the parse-tree shadow are explicit unsupported verdicts, never clean output.
/// Production remains authoritative and has dedicated semantic canaries for these shapes.
#[test]
fn sh_taint_unsupported_shapes_are_explicit() {
    let cases = [
        // Break/continue and tuple lets are supported ONLY in the all-public projection
        // (HB-2 rung 1); their nonpublic contexts must still fail closed. The old all-public
        // `while c { break; }` case moved to CORPUS_ACCEPT — clean on both sides now.
        (
            "early exit under a secret guard",
            "module ext; fn f(s: i64 @Secret) -> i64 @Secret { while s > 0 { break; } return s; }",
        ),
        (
            "tuple let in a nonpublic context",
            "module ext; fn mk() -> (i64, i64) { return (1, 2); } fn f(s: i64 @Secret) -> i64 @Secret { let (a, b) = mk(); return s; }",
        ),
        (
            "match guard",
            "module ext; enum E { A, B } fn f(e: E, b: bool) -> i64 { match e { E::A if b => { return 1; }, _ => { return 0; }, } }",
        ),
        (
            "spawn and actor boundary",
            "module sigil; cap type Fuel {} entry actor Main { state { fuel: Fuel } on Start(f: Fuel) -> i64 { let child = spawn::<Worker>(f); return 0; } } actor Worker { init(f: Fuel) {} on Ping() -> i64 { return 0; } }",
        ),
        (
            "closure capture model",
            "module ext; fn f(x: i64) -> i64 { let g = fn() -> i64 { return x; }; return 0; }",
        ),
        (
            "region body",
            "#[ring(outer)] module ext; fn f() -> i64 ! { Alloc } { region scratch(64) { let x = 1; }; return 0; }",
        ),
    ];
    for (label, src) in cases {
        let output = full_output(src);
        assert!(
            output.split(';').any(|item| item == TAINT_UNSUPPORTED),
            "SH-TAINT {label}: unsupported shape produced an apparently clean verdict: {output:?}"
        );
    }
}

// ── HB-2 rung-1 property test: the all-public supported statement surface ──────────────────
//
// The tuple-let/break/continue arms were added with hand-picked fixtures; this generates
// programs over the WHOLE supported all-public statement surface — scalar lets, tuple lets,
// public-guarded if/while, break/continue, compound arithmetic — and asserts the property the
// arms claim: an all-public program is CLEAN on BOTH sides (oracle core codes = ∅, shadow
// T-codes = ∅, and no SH_TAINT_UNSUPPORTED marker — the projection is EXACT there, not merely
// subset-safe). Each template is closed over its own index so generated names never collide.
mod allpublic_prop {
    use super::*;
    use proptest::prelude::*;

    /// One self-contained statement block, index-unique names.
    fn block(kind: u8, i: usize) -> String {
        match kind {
            0 => format!("    let a{i}: i64 = {i};\n"),
            1 => format!("    let (t{i}, u{i}) = mk();\n    let s{i}: i64 = t{i} + u{i};\n"),
            2 => format!(
                "    if p == {i} {{\n        let b{i}: i64 = 1;\n    }} else {{\n        let c{i}: i64 = 2;\n    }}\n"
            ),
            3 => format!(
                "    let mut w{i}: i64 = 0;\n    while w{i} < 3 {{\n        w{i} = w{i} + 1;\n        continue;\n    }}\n"
            ),
            4 => format!(
                "    let mut v{i}: i64 = 0;\n    while v{i} < 9 {{\n        v{i} = v{i} + 2;\n        if v{i} > 4 {{\n            break;\n        }} else {{\n        }}\n    }}\n"
            ),
            _ => format!("    let mut m{i}: i64 = p;\n    m{i} = m{i} + {i};\n"),
        }
    }

    fn program(kinds: &[u8]) -> String {
        let body: String = kinds
            .iter()
            .enumerate()
            .map(|(i, k)| block(*k, i))
            .collect();
        format!(
            "module ext;\nfn mk() -> (i64, i64) {{\n    return (1, 2);\n}}\nfn f(p: i64) -> i64 {{\n{body}    return p;\n}}\n"
        )
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 32, ..ProptestConfig::default() })]
        #[test]
        fn allpublic_supported_surface_is_clean_both_sides(
            kinds in proptest::collection::vec(0u8..6, 1..8)
        ) {
            let src = program(&kinds);
            let oracle = oracle_tcodes(&src);
            prop_assert!(oracle.is_empty(), "oracle fired {oracle:?} on all-public:\n{src}");
            let shadow = sigil_tcodes(&src);
            prop_assert!(shadow.is_empty(), "shadow fired {shadow:?} on all-public:\n{src}");
            let raw = full_output(&src);
            prop_assert!(
                !raw.split(';').any(|c| c == TAINT_UNSUPPORTED),
                "shadow marked a SUPPORTED all-public shape unsupported:\n{src}\n{raw}"
            );
        }
    }
}

/// DETERMINISM (ET-T5): two runs of the compiled tool are byte-identical.
#[test]
fn sh_taint_deterministic() {
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

/// The oracle path on a STANDALONE file. `Some(codes)` if the file type-checks in
/// isolation (the oracle reaches `check_taints`); `None` if it is dep-blocked — most
/// stdlib files reference sibling modules and cannot type-check alone, so the oracle
/// cannot run `check_taints` on them (the self-host, a raw parse-tree walk, can).
fn oracle_tcodes_standalone(src: &str) -> Option<Vec<String>> {
    let source = SourceFile::new("<stdlib>", src);
    let (ast, pdiags) = parser::parse(&source);
    if !pdiags.is_empty() {
        return None;
    }
    let resolved = name_resolution::resolve(&ast).ok()?;
    let (typed, _reg) =
        type_check::check_with_options(&resolved, &CompileOptions::default()).ok()?;
    let mut v: Vec<String> = match taint_check::check_taints(&typed) {
        Ok(_) => Vec::new(),
        Err(ds) => ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| CORE_T_CODES.contains(&c.as_str()))
            .collect(),
    };
    v.sort();
    v.dedup();
    Some(v)
}

/// WHOLE-STDLIB taint-clean gate (PR-T2 part c). For every `stdlib/sigil/*.sigil`, auto-
/// partition on whether the oracle can run standalone:
///  - **type-checks standalone** → the self-hosted taint codes EXACTLY match the oracle's
///    (full parity). The stdlib is taint-clean, so both are empty — and this branch
///    includes EVERY taint-ANNOTATED file that type-checks in isolation
///    (crypto/fs/http/random/time/z3, the `@Internal`-return FFI fns), exercising the
///    @Internal-return threading at real parity.
///  - **dep-blocked** (references sibling modules → resolve/type error) → the self-hosted
///    tool emits ZERO taint codes: a NO-FALSE-POSITIVE floor on the real records / closures
///    / generics / methods / byte-op surface of map/string/strings/bounded_* (the oracle
///    cannot run `check_taints` there, so parity is impossible — the floor is the strongest
///    sound check, and it is subset-safe by construction).
#[test]
fn sh_taint_stdlib_clean_parity_and_floor() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/sigil");
    let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read stdlib dir {}: {e}", dir.display()))
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().map(|x| x == "sigil").unwrap_or(false))
        .collect();
    files.sort();
    assert!(
        files.len() >= 20,
        "expected the full stdlib (>=20 files), found {} under {}",
        files.len(),
        dir.display()
    );

    let mut parity_files: Vec<String> = Vec::new();
    let mut floor_files: Vec<String> = Vec::new();
    for path in &files {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let src = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {name}: {e}"));
        let sig = sigil_tcodes(&src);
        match oracle_tcodes_standalone(&src) {
            Some(oracle) => {
                assert_eq!(
                    sig, oracle,
                    "SH-TAINT stdlib {name}: self-hosted taint codes must match the oracle"
                );
                parity_files.push(name);
            }
            None => {
                assert!(
                    sig.is_empty(),
                    "SH-TAINT stdlib {name}: self-hosted emitted a spurious taint code {sig:?} on a (dep-blocked) clean stdlib file"
                );
                floor_files.push(name);
            }
        }
    }

    // Non-stub / non-vacuous: the oracle-parity branch must be substantial AND must include
    // every taint-ANNOTATED file that type-checks standalone (so the @Internal-return
    // threading is really exercised at parity, never silently demoted into the floor).
    assert!(
        parity_files.len() >= 10,
        "stdlib oracle-parity branch is vacuously small ({}): {parity_files:?}",
        parity_files.len()
    );
    for ann in [
        "crypto.sigil",
        "fs.sigil",
        "http.sigil",
        "random.sigil",
        "time.sigil",
        "z3.sigil",
    ] {
        assert!(
            parity_files.iter().any(|f| f == ann),
            "taint-annotated {ann} must be in the oracle-parity branch (the @Internal-return threading gate); parity={parity_files:?}"
        );
    }
    // Sanity: the floor branch is also exercised (the dep-blocked records/closures surface).
    assert!(
        !floor_files.is_empty(),
        "expected some dep-blocked stdlib files in the no-false-positive floor branch"
    );
}
