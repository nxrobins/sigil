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
//!
//! SHP-5a: the shadow carries production's control-flow join model (`if`/`while`/`for`/
//! `match` merges, `break`/`continue`/`return` divergence, the continuation taint, block
//! shadow restores, the loop-head fixpoint) and its M6 region model (`alloc` regions,
//! aliases, raw stores), so nonpublic values under control flow are checked rather than
//! refused.
//!
//! SHP-5c-1: the shadow reads the `split`/`draw` amount (T027 / T001) and carries
//! production's intraprocedural heap floors — the raw-load and typed-read floors raised by
//! an FFI boundary (S1), a heap-resident value at a non-public label (S2, at entry and at
//! every materialisation), a raw store (S4/S6) and a projected-place write (S6/S7), and
//! joined into every raw load and typed read (an element, field or slice projection, a `?`,
//! an intrinsic, a heap-typed local, a `str` literal, S11) — on a syntactic typing that
//! refuses what it cannot classify at a non-public label.
//!
//! SHP-5c-2: the shadow carries production's call-site summaries — per function, what a
//! call to it can have written (S5: the floors raised at the site's taint joined with the
//! callee's own annotation bound, and the regions of the arguments it writes through, by
//! parameter slot) and read (S8: the caller's floors joined into the result), a syntactic
//! scan closed over the call graph as production's — and refuses a call site whose callee
//! it cannot name (a call through a local, a `grant` of a closure held in a local) or whose
//! summary carries a fact its typing cannot decide, wherever a label makes the summaries
//! live — an effect operation's parameter label included, which production's program-wide
//! bound folds in and the shadow reads off the operation's own parameter nodes. Nothing the
//! oracle derives from the heap floors stays oracle-only; every rule has a reject and a
//! clean twin below, and every refusal of a program-wide-bound site a label-free twin.

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
/// Two oracle codes are deliberately OUTSIDE it and so oracle-only: T033 (CT018, `str`
/// content compare) and T034 (CT008, `@SecretCT` shift amount). The shadow has neither
/// rule; filtering them here means the shadow LAGS the oracle on those two rather than
/// disagreeing with it, and adding either to this set without a shadow rule turns the
/// differential red (fails closed).
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
/// The property tests' case budget: `default_cases` (what CI runs) unless `PROPTEST_CASES`
/// names another count, the way a larger local run is taken. An explicit `cases` field would
/// otherwise override the variable `ProptestConfig::default()` reads, and a documented
/// 256-case measurement would have run 32.
fn case_budget(default_cases: u32) -> u32 {
    std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|value| value.parse::<u32>().ok())
        .unwrap_or(default_cases)
}

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
    // ── M6 region fixtures (SHP-5a) ──
    // The M5b/M6 store8-launder rejects were withdrawn at the agentic-bench merge
    // (2026-07-29) because the selfhost mirror lacked the region model. SHP-5a mirrors it
    // (`tt_regions_of_value` / `tt_rt_*` in `selfhost/taint_check.sigil`), so they return:
    // a @Secret stored through a pointer taints the pointer's REGION, and a sink that hands
    // the pointer on unread (`return out`) reads that taint. The clean twins stay in
    // CORPUS_ACCEPT.
    (
        "M6 store8 secret then return the base pointer -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let out: i64 = alloc(8);\n    store8(out, s);\n    return out;\n}\n",
        &["T001"],
    ),
    // An alias taken BEFORE the store sees the taint: regions, not names, carry it.
    (
        "M6 alias taken before the secret store -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let out: i64 = alloc(8);\n    let q: i64 = out;\n    store8(out, s);\n    return q;\n}\n",
        &["T001"],
    ),
    // The round-7 loop back-edge: `q` points into `out`'s region from the second iteration on,
    // which only the loop-head fixpoint (region sets joined by union) can see.
    (
        "M6 pointer rebound across a loop back-edge taints the returned region -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let mut q: i64 = alloc(8);\n    let mut i: i64 = 0;\n    while i < 2 {\n        store8(q, s);\n        q = out;\n        i = i + 1;\n    }\n    return out;\n}\n",
        &["T001"],
    ),
    // The same rebind split across `if` arms: after the merge `q` has BOTH candidates.
    (
        "M6 pointer rebound on one if-arm taints every candidate region -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret, p: i64) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let mut q: i64 = alloc(8);\n    if p > 0 {\n        q = out;\n    } else {\n        q = alloc(8);\n    }\n    store8(q, s);\n    return out;\n}\n",
        &["T001"],
    ),
    // Round 8: `alloc(8) + 4` mints a region like a bare `alloc(8)`.
    (
        "M6 alloc plus an offset is a regioned local -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8) + 4;\n    store8(q, s);\n    return q;\n}\n",
        &["T001"],
    ),
    // The ADDRESS is an operand too: a @Public byte at a secret-derived address changes WHICH
    // cell the host sees, so the region takes the join of every operand.
    (
        "M6 public byte at a secret-derived address taints the region -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    store8(out + (s & 1), 9);\n    return out;\n}\n",
        &["T001"],
    ),
    // ── SHP-5a control-flow join fixtures ──
    // Each isolates one code produced ONLY by the join model (a straight-line reading of the
    // same program is clean); its twin in CORPUS_ACCEPT is the same program with the sink
    // annotated, so an over-approximating merge would fail the twin and a missing merge
    // would fail the reject.
    // A record raised under a secret pc on ONE path is secret after the merge.
    (
        "SHP-5a if-join: record raised on one path, read public after the merge -> T001",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret, p: i64) -> i64 {\n    let mut r: R = R { a: 0, b: 0 };\n    if s > 0 {\n        r.a = p;\n    } else {\n    }\n    let y: i64 @Public = r.b;\n    return 0;\n}\n",
        &["T001"],
    ),
    // Reaching the code after a one-sided `return` reveals the condition: the continuation
    // taint folds into the later `let`.
    (
        "SHP-5a one-sided return taints the continuation -> T001",
        "module ext;\nfn f(s: i64 @Secret) -> i64 @Secret {\n    if s > 0 {\n        return s;\n    } else {\n    }\n    let y: i64 = 0;\n    return s;\n}\n",
        &["T001"],
    ),
    // A secret-guarded `break`: the loop exit joins the break frame, and the statements the
    // exit skipped ran under the secret continuation, so `i` is secret at the return.
    (
        "SHP-5a secret-guarded break: the loop exit carries the condition -> T001",
        "module ext;\nfn f(s: i64 @Secret) -> i64 {\n    let mut i: i64 = 0;\n    while i < 10 {\n        if s > i {\n            break;\n        }\n        i = i + 1;\n    }\n    return i;\n}\n",
        &["T001"],
    ),
    // The loop-head FIXPOINT: the read precedes the raise in the body, so only the second
    // pass (head = pre ⊔ body end) sees the record secret at the read.
    (
        "SHP-5a loop-carried join reaches the read on the second pass -> T001",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret, n: i64) -> i64 {\n    let mut r: R = R { a: 0, b: 0 };\n    let mut i: i64 = 0;\n    while i < n {\n        let y: i64 @Public = r.b;\n        if s > 0 {\n            r.a = i;\n        } else {\n        }\n        i = i + 1;\n    }\n    return 0;\n}\n",
        &["T001"],
    ),
    // A range over a secret bound fixes a secret body pc.
    (
        "SHP-5a for-range over a secret bound taints the body -> T001",
        "module ext;\nfn f(s: i64 @Secret) -> i64 @Secret {\n    for i in 0..s {\n        let y: i64 = 0;\n    }\n    return s;\n}\n",
        &["T001"],
    ),
    // A for-in over a secret array binds a secret element.
    (
        "SHP-5a for-in over a secret array binds a secret element -> T001",
        "module ext;\nfn f(arr: [i64; 4] @Secret) -> i64 @Secret {\n    let mut t: i64 @Secret = 0;\n    for x in arr {\n        let y: i64 = x;\n        t = x;\n    }\n    return t;\n}\n",
        &["T001"],
    ),
    // A pattern binding under a secret scrutinee carries the scrutinee's taint.
    (
        "SHP-5a match arm: payload bound under a secret scrutinee -> T001",
        "module ext;\nenum E { A(i64), B }\nfn f(e: E @Secret) -> i64 @Secret {\n    match e {\n        E::A(v) => { let y: i64 = v; },\n        E::B => { },\n    }\n    return 0;\n}\n",
        &["T001"],
    ),
    // A `let` that shadows an outer secret inside a block is restored at the block's end:
    // the read after the `if` is the OUTER secret `x`.
    (
        "SHP-5a block shadow restored: the outer secret is read after the block -> T001",
        "module ext;\nfn f(s: i64 @Secret, p: i64) -> i64 {\n    let x: i64 @Secret = s;\n    if p > 0 {\n        let x: i64 = 0;\n    } else {\n    }\n    let y: i64 = x;\n    return 0;\n}\n",
        &["T001"],
    ),
    // A call under a secret pc hands the pc to the callee's @Public parameter.
    (
        "SHP-5a call argument under a secret pc -> T001",
        "module ext;\nfn g(v: i64) -> i64 { return v; }\nfn f(s: i64 @Secret) -> i64 @Secret {\n    if s > 0 {\n        let r: i64 @Secret = g(1);\n    } else {\n    }\n    return s;\n}\n",
        &["T001"],
    ),
    // ── SHP-5c-1 fixtures: the capability quantity rule and the intraprocedural heap floors ──
    // Each isolates one code produced ONLY by the rule named (its twin in CORPUS_ACCEPT is the
    // same program with the sink annotated or the source made public), so an over-
    // approximating floor would fail the twin and a missing one would fail the reject.
    (
        "SHP-5c-1 split amount @Secret -> T001",
        "module ext;\ncap type Fuel {}\nfn f(c: Fuel, s: i64 @Secret) -> i64 {\n    let d: Fuel = c.split(s);\n    return 0;\n}\n",
        &["T001"],
    ),
    (
        "SHP-5c-1 draw amount @SecretCT -> T027",
        "module ext;\ncap type Fuel {}\nfn f(c: Fuel, k: i64 @SecretCT) -> i64 {\n    let d: Fuel = c.draw(k);\n    return 0;\n}\n",
        &["T027"],
    ),
    // S2 (the case the summary-lag pin held until SHP-5c-1): a non-@Public
    // raw store raises the function's raw-load floor, so a later load8 through an UNRELATED
    // region is secret — the floor is address-blind where the region is not.
    (
        "SHP-5c-1 S2 raw-load floor after a secret store -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let out: i64 = alloc(8);\n    let q: i64 = alloc(8);\n    store8(out, s);\n    let v: i64 = load8(q);\n    return v;\n}\n",
        &["T001"],
    ),
    // S1: the host wrote guest memory before the extern returned; every raw load after it is
    // @Internal at best.
    (
        "SHP-5c-1 S1 extern call floors a later raw load -> T001",
        "#[ring(outer)] module ext;\nextern \"C\" fn k(x: i64) -> i64 ! { FFI, Unsafe };\nfn f(p: i64) -> i64 @Internal ! { FFI, Unsafe, Alloc } {\n    let r: i64 @Internal = k(p);\n    let q: i64 = alloc(8);\n    let v: i64 = load8(q);\n    return r;\n}\n",
        &["T001"],
    ),
    // S1 through a callee: a function whose effect row names FFI may have crossed the boundary.
    (
        "SHP-5c-1 S1 callee with FFI in its row floors the caller's raw loads -> T001",
        "#[ring(outer)] module ext;\nextern \"C\" fn k(x: i64) -> i64 ! { FFI, Unsafe };\nfn g(p: i64) -> i64 @Internal ! { FFI, Unsafe } {\n    let r: i64 @Internal = k(p);\n    return r;\n}\nfn f(p: i64) -> i64 @Internal ! { FFI, Unsafe, Alloc } {\n    let r: i64 @Internal = g(p);\n    let q: i64 = alloc(8);\n    let v: i64 = load8(q);\n    return r;\n}\n",
        &["T001"],
    ),
    // S1 through a user type's method, resolved by the impl table.
    (
        "SHP-5c-1 S1 method with FFI in its row floors the caller's raw loads -> T001",
        "#[ring(outer)] module ext;\nextern \"C\" fn k(x: i64) -> i64 ! { FFI, Unsafe };\nrecord R { a: i64 }\nimpl R {\n    fn poke(self: R) -> i64 @Internal ! { FFI, Unsafe } {\n        let r: i64 @Internal = k(self.a);\n        return r;\n    }\n}\nfn f(r: R) -> i64 @Internal ! { FFI, Unsafe, Alloc } {\n    let x: i64 @Internal = r.poke();\n    let q: i64 = alloc(8);\n    let v: i64 = load8(q);\n    return x;\n}\n",
        &["T001"],
    ),
    // S2 at entry: a heap-typed parameter's bytes are already in linear memory at its label.
    (
        "SHP-5c-1 S2 heap-typed @Secret parameter floors raw loads at entry -> T001",
        "#[ring(outer)] module ext;\nfn f(s: str @Secret) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    let v: i64 = load8(q);\n    return v;\n}\n",
        &["T001"],
    ),
    // S2 at a materialisation: a heap-resident value built under a secret pc is bytes in
    // memory at that pc (a `str` literal here; the twin builds a scalar).
    (
        "SHP-5c-1 S2 str literal materialised under a secret pc floors raw loads -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    if s > 0 {\n        let t: str @Secret = \"abc\";\n    } else {\n    }\n    let v: i64 = load8(q);\n    return v;\n}\n",
        &["T001"],
    ),
    // S4: a raw store at an unchecked address may sit inside a live aggregate, so a later
    // typed read — an element here, a method intrinsic and a heap-typed local below — is
    // floored too.
    (
        "SHP-5c-1 S4 secret raw store floors a later element read -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret, arr: [i64; 4]) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    store8(q, s);\n    let y: i64 = arr[0];\n    return 0;\n}\n",
        &["T001"],
    ),
    (
        "SHP-5c-1 S4 secret raw store floors a later str intrinsic -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret, t: str) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    store8(q, s);\n    let n: i64 = t.len();\n    return 0;\n}\n",
        &["T001"],
    ),
    (
        "SHP-5c-1 S4 secret raw store floors a later heap-typed local read -> T001",
        "#[ring(outer)] module ext;\nrecord R { a: i64 }\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let r: R = R { a: 1 };\n    let q: i64 = alloc(8);\n    store8(q, s);\n    let y: R = r;\n    return 0;\n}\n",
        &["T001"],
    ),
    // S11: a `str` literal's bytes are shared static data a raw store can change.
    (
        "SHP-5c-1 S11 str literal after a secret raw store reads floored static data -> T001",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    store8(q, s);\n    let t: str = \"abc\";\n    return 0;\n}\n",
        &["T001"],
    ),
    // S6: a @Public byte at a secret-derived index — WHICH element changed is the secret, and
    // a later typed read of the array recovers it.
    (
        "SHP-5c-1 S6 public element write at a secret index floors typed reads -> T001",
        "module ext;\nfn f(s: i64 @Secret) -> i64 {\n    let mut a: [i64; 2] = [0, 0];\n    a[s & 1] = 1;\n    let y: i64 = a[0];\n    return 0;\n}\n",
        &["T001"],
    ),
    // S7: a projected write labels the root name, but records are reference-semantic — an
    // alias taken before the write reads the secret back through a typed read.
    (
        "SHP-5c-1 S7 secret projected write read back through an alias -> T001",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret) -> i64 {\n    let mut r: R = R { a: 0, b: 0 };\n    let b: R = r;\n    r.a = s;\n    let y: i64 = b.b;\n    return 0;\n}\n",
        &["T001"],
    ),
    // ── SHP-5c-2 fixtures: the call-site summaries ──
    // Each isolates one code produced ONLY by a callee's summary applied at its call site (its
    // twin in CORPUS_ACCEPT keeps the call and removes what the summary carries), so a summary
    // applied too widely fails the twin and one applied too narrowly fails the reject.
    // S5: the callee stores its own secret through the CALLER's pointer; the summary taints the
    // argument's region at the call site (the pointer reaches the sink unread).
    (
        "SHP-5c-2 S5 callee writes its secret through the caller's buffer -> T001",
        "module tool;\nfn poke(out: i64) -> i64 {\n    let s: i64 @Secret = 1;\n    store8(out, s);\n    return 1;\n}\npub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let n: i64 = poke(out);\n    return out << 32 | n;\n}\n",
        &["T001"],
    ),
    // S5, by slot: the callee writes through its SECOND parameter, so the region tainted is the
    // second argument's (the twin swaps the arguments).
    (
        "SHP-5c-2 S5 the callee writes through its second parameter -> T001",
        "module tool;\nfn poke(out: i64, scratch: i64) -> i64 {\n    let s: i64 @Secret = 1;\n    store8(scratch, s & 1);\n    return 1;\n}\npub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let scratch: i64 = alloc(8);\n    let n: i64 = poke(scratch, out);\n    return out << 32 | n;\n}\n",
        &["T001"],
    ),
    // S5, transitively: the write is in a callee of the callee, reached through an alias of the
    // parameter — the call-graph closure and the rooted map together.
    (
        "SHP-5c-2 S5 through an alias and a callee of the callee -> T001",
        "module tool;\nfn inner(q: i64) -> i64 {\n    let s: i64 @Secret = 1;\n    let r: i64 = q + 1;\n    store8(r, s & 1);\n    return 1;\n}\nfn poke(out: i64) -> i64 {\n    let alias: i64 = out;\n    return inner(alias);\n}\npub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let n: i64 = poke(out);\n    return out << 32 | 2;\n}\n",
        &["T001"],
    ),
    // S5, the floors: a callee that only MATERIALISES a secret aggregate (it stores nothing at an
    // existing address) raises the caller's raw-load floor, so a later raw load is secret.
    (
        "SHP-5c-2 S5 a materialising callee floors the caller's raw loads -> T001",
        "#[ring(outer)] module ext;\nfn mk() -> i64 {\n    let s: i64 @Secret = 1;\n    let a: [i64; 2] @Secret = [s, 0];\n    return 0;\n}\nfn f() -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    let z: i64 = mk();\n    let v: i64 = load8(q);\n    return v;\n}\n",
        &["T001"],
    ),
    // S5, the counted cost production pins (its `annotation` is a syntactic bound): a callee that
    // MENTIONS a secret it never writes still floors the call site.
    (
        "SHP-5c-2 S5 a callee that mentions a secret it never writes still floors -> T001",
        "module tool;\nfn poke(out: i64) -> i64 {\n    let s: i64 @Secret = 1;\n    store8(out, 7);\n    return 1;\n}\npub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let n: i64 = poke(out);\n    return out << 32 | n;\n}\n",
        &["T001"],
    ),
    // S5 through an impl method: the store goes through `self`, and the summary (keyed by the
    // receiver's type) raises the caller's floors.
    (
        "SHP-5c-2 S5 an impl method storing its secret through self floors the caller -> T001",
        "#[ring(outer)] module ext;\nrecord B { p: i64 }\nimpl B {\n    fn put(self: B) -> i64 {\n        let s: i64 @Secret = 1;\n        store8(self.p, s);\n        return 1;\n    }\n}\nfn f() -> i64 ! { Alloc } {\n    let b: B = B { p: alloc(8) };\n    let n: i64 = b.put();\n    let v: i64 = load8(b.p);\n    return v;\n}\n",
        &["T001"],
    ),
    // S8: the callee raw-reads memory the caller's secret store dirtied; its result carries the
    // caller's raw-load floor.
    (
        "SHP-5c-2 S8 callee reads the caller's floored bytes into its result -> T001",
        "#[ring(outer)] module ext;\nfn peek(p: i64) -> i64 {\n    let b: i64 = load8(p);\n    return b;\n}\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let out: i64 = alloc(8);\n    let q: i64 = alloc(8);\n    store8(out, s);\n    let v: i64 = peek(q);\n    return v;\n}\n",
        &["T001"],
    ),
    // S8, typed: a callee whose only read is typed (a `str` literal's length) carries the
    // caller's typed-read floor, raised here by a secret projected write.
    (
        "SHP-5c-2 S8 a callee's typed read carries the caller's typed floor -> T001",
        "module ext;\nfn helper() -> i64 {\n    let t: str = \"abc\";\n    return t.len();\n}\nfn f(s: i64 @Secret) -> i64 {\n    let mut a: [i64; 2] = [0, 0];\n    a[0] = s;\n    let n: i64 = helper();\n    return n;\n}\n",
        &["T001"],
    ),
    // S5, by slot through a nested call: the callee's write-through slot reaches the caller's
    // parameter through an argument list whose FIRST argument is itself a call. Each edge's
    // argument roots are its own (production's per-edge vector), not those of the call nested
    // inside it (the twin swaps the outer arguments).
    (
        "SHP-5c-2 S5 the written-through slot is found past a call nested in the arguments -> T001",
        "module tool;\nfn id(x: i64) -> i64 {\n    return x;\n}\nfn inner(a: i64, b: i64) -> i64 {\n    let s: i64 @Secret = 1;\n    store8(b, s & 1);\n    return 1;\n}\nfn poke(x: i64, y: i64) -> i64 {\n    return inner(id(y), x);\n}\npub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let scratch: i64 = alloc(8);\n    let n: i64 = poke(out, scratch);\n    return out << 32 | n;\n}\n",
        &["T001"],
    ),
    // SHP-5c-3: a region body is checked as a block of its function at the same pc — a
    // downgrade inside it is the T001 of any block, and a secret written through a record
    // bound before the body is read back after it.
    (
        "SHP-5c-3 downgrade inside a region body -> T001",
        "#[ring(outer)] module ext;\nfn leak(secret: i64 @Secret) -> i64 ! { Alloc } {\n    region scratch(64) {\n        let exposed: i64 @Public = secret;\n    };\n    return 0;\n}\n",
        &["T001"],
    ),
    (
        "SHP-5c-3 a secret written through an outer record inside a region body, read after it -> T001",
        "#[ring(outer)] module ext;\nrecord P { x: i64 }\nfn f(secret: i64 @Secret) -> i64 ! { Alloc } {\n    let mut p: P = P { x: 0 };\n    region scratch(64) {\n        p.x = secret;\n    };\n    return p.x;\n}\n",
        &["T001"],
    ),
    // SHP-5c-3: a region's limit is its allocation size, observable through the heap layout, so
    // a @SecretCT limit is T029.
    (
        "SHP-5c-3 a @SecretCT region limit -> T029",
        "#[ring(outer)] module ext;\nfn f(s: i64 @SecretCT) -> i64 ! { Alloc } { region scratch(s) { let x: i64 = 1; }; return 0; }\n",
        &["T029"],
    ),
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
    // machinery only). Public instances are clean on BOTH sides. SHP-5a modelled the nonpublic
    // `break`/`continue` (the join fixtures below); a tuple let under a nonpublic pc is still
    // refused in `sh_taint_unsupported_shapes_are_explicit`.
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
    // ── SHP-5a twins: the join-model rejects with their sink annotated — clean ──
    (
        "SHP-5a if-join twin — record raised on one path, read at @Secret — clean",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret, p: i64) -> i64 {\n    let mut r: R = R { a: 0, b: 0 };\n    if s > 0 {\n        r.a = p;\n    } else {\n    }\n    let y: i64 @Secret = r.b;\n    return 0;\n}\n",
    ),
    (
        "SHP-5a continuation twin — the let after a one-sided return is @Secret — clean",
        "module ext;\nfn f(s: i64 @Secret) -> i64 @Secret {\n    if s > 0 {\n        return s;\n    } else {\n    }\n    let y: i64 @Secret = 0;\n    return s;\n}\n",
    ),
    (
        "SHP-5a break twin — the loop counter returned at @Secret — clean",
        "module ext;\nfn f(s: i64 @Secret) -> i64 @Secret {\n    let mut i: i64 = 0;\n    while i < 10 {\n        if s > i {\n            break;\n        }\n        i = i + 1;\n    }\n    return i;\n}\n",
    ),
    (
        "SHP-5a fixpoint twin — the loop-carried read is @Secret — clean",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret, n: i64) -> i64 {\n    let mut r: R = R { a: 0, b: 0 };\n    let mut i: i64 = 0;\n    while i < n {\n        let y: i64 @Secret = r.b;\n        if s > 0 {\n            r.a = i;\n        } else {\n        }\n        i = i + 1;\n    }\n    return 0;\n}\n",
    ),
    (
        "SHP-5a for-range twin — the body let is @Secret — clean",
        "module ext;\nfn f(s: i64 @Secret) -> i64 @Secret {\n    for i in 0..s {\n        let y: i64 @Secret = i;\n    }\n    return s;\n}\n",
    ),
    (
        "SHP-5a for-in twin — the element is bound at @Secret — clean",
        "module ext;\nfn f(arr: [i64; 4] @Secret) -> i64 @Secret {\n    let mut t: i64 @Secret = 0;\n    for x in arr {\n        let y: i64 @Secret = x;\n        t = x;\n    }\n    return t;\n}\n",
    ),
    (
        "SHP-5a match twin — the payload is bound at @Secret — clean",
        "module ext;\nenum E { A(i64), B }\nfn f(e: E @Secret) -> i64 @Secret {\n    match e {\n        E::A(v) => { let y: i64 @Secret = v; },\n        E::B => { },\n    }\n    return 0;\n}\n",
    ),
    // The inverse shadow: a SECRET shadow inside the block must not leak onto the outer
    // public `x` (a restore that kept the inner binding would be a false T001 here).
    (
        "SHP-5a shadow twin — an inner secret shadow does not reach the outer name — clean",
        "module ext;\nfn f(s: i64 @Secret, p: i64) -> i64 {\n    let x: i64 = 0;\n    if p > 0 {\n        let x: i64 @Secret = s;\n    } else {\n    }\n    let y: i64 = x;\n    return y;\n}\n",
    ),
    (
        "SHP-5a call twin — the callee parameter is @Secret — clean",
        "module ext;\nfn g(v: i64 @Secret) -> i64 @Secret { return v; }\nfn f(s: i64 @Secret) -> i64 @Secret {\n    if s > 0 {\n        let r: i64 @Secret = g(1);\n    } else {\n    }\n    return s;\n}\n",
    ),
    // The pc is restored after a secret-guarded `if` with no divergence: the code after it
    // is public again (the shape the pre-SHP-5a shadow refused outright).
    (
        "SHP-5a secret guard with no leak — the pc is restored after the if — clean",
        "module ext;\nfn f(s: i64 @Secret, p: i64) -> i64 {\n    let mut x: i64 = p;\n    if s > 0 {\n    } else {\n    }\n    x = x + 1;\n    return x;\n}\n",
    ),
    // The two shapes SHP-5a lifted out of `sh_taint_unsupported_shapes_are_explicit`.
    (
        "SHP-5a early exit under a secret guard — clean (was a refused canary)",
        "module ext; fn f(s: i64 @Secret) -> i64 @Secret { while s > 0 { break; } return s; }",
    ),
    (
        "SHP-5a tuple let beside a secret parameter, public pc — clean (was a refused canary)",
        "module ext; fn mk() -> (i64, i64) { return (1, 2); } fn f(s: i64 @Secret) -> i64 @Secret { let (a, b) = mk(); return s; }",
    ),
    // ── M6 twins: rebinding to a FRESH region drops the old one (no false alias positive) ──
    (
        "M6 loop rebind to a fresh alloc every iteration keeps the returned region clean",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let mut q: i64 = alloc(8);\n    let mut i: i64 = 0;\n    while i < 2 {\n        store8(q, s);\n        q = alloc(8);\n        i = i + 1;\n    }\n    return out;\n}\n",
    ),
    (
        "M6 rebind to a fresh alloc on BOTH if-arms keeps the returned region clean",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret, p: i64) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let mut q: i64 = alloc(8);\n    if p > 0 {\n        q = alloc(8);\n    } else {\n        q = alloc(8);\n    }\n    store8(q, s);\n    return out;\n}\n",
    ),
    // A block shadow restores the outer REGION too: the secret went into the inner buffer.
    (
        "M6 secret stored into a shadowing inner buffer leaves the outer pointer clean",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret, p: i64) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    if p > 0 {\n        let out: i64 = alloc(8);\n        store8(out, s);\n    } else {\n    }\n    return out;\n}\n",
    ),
    // ── SHP-5c-1 twins ──
    (
        "SHP-5c-1 split amount @Public — clean",
        "module ext;\ncap type Fuel {}\nfn f(c: Fuel, s: i64) -> i64 {\n    let d: Fuel = c.split(s);\n    return 0;\n}\n",
    ),
    (
        "SHP-5c-1 S1 twin — the raw load after the extern call is bound @Internal — clean",
        "#[ring(outer)] module ext;\nextern \"C\" fn k(x: i64) -> i64 ! { FFI, Unsafe };\nfn f(p: i64) -> i64 @Internal ! { FFI, Unsafe, Alloc } {\n    let r: i64 @Internal = k(p);\n    let q: i64 = alloc(8);\n    let v: i64 @Internal = load8(q);\n    return r;\n}\n",
    ),
    // The critical no-false-positive: a SCALAR under a secret pc is a wasm local, not bytes in
    // memory — no floor rises, and the later raw load stays public.
    (
        "SHP-5c-1 S2 twin — a scalar under a secret pc raises no floor — clean",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    if s > 0 {\n        let t: i64 @Secret = s + 1;\n    } else {\n    }\n    let v: i64 = load8(q);\n    return v;\n}\n",
    ),
    // A plain re-read of a heap-typed local allocates nothing: exempt from S2.
    (
        "SHP-5c-1 S2 twin — a public heap local re-read under a secret pc raises no floor — clean",
        "#[ring(outer)] module ext;\nrecord R { a: i64 }\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let r: R = R { a: 1 };\n    let q: i64 = alloc(8);\n    if s > 0 {\n        let y: R @Secret = r;\n    } else {\n    }\n    let v: i64 = load8(q);\n    return v;\n}\n",
    ),
    (
        "SHP-5c-1 entry twin — a heap-typed public parameter floors nothing — clean",
        "#[ring(outer)] module ext;\nfn f(s: str) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    let v: i64 = load8(q);\n    return v;\n}\n",
    ),
    (
        "SHP-5c-1 S4 twin — the element read after the secret store is bound @Secret — clean",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret, arr: [i64; 4]) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    store8(q, s);\n    let y: i64 @Secret = arr[0];\n    return 0;\n}\n",
    ),
    (
        "SHP-5c-1 S11 twin — the str literal after the secret store is bound @Secret — clean",
        "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    store8(q, s);\n    let t: str @Secret = \"abc\";\n    return 0;\n}\n",
    ),
    (
        "SHP-5c-1 S6 twin — a public element write at a public index floors nothing — clean",
        "module ext;\nfn f(s: i64 @Secret) -> i64 {\n    let mut a: [i64; 2] = [0, 0];\n    a[1] = 1;\n    let y: i64 = a[0];\n    return 0;\n}\n",
    ),
    (
        "SHP-5c-1 S7 twin — a public projected write under a public pc floors nothing — clean",
        "module ext;\nrecord R { a: i64, b: i64 }\nfn f(s: i64 @Secret) -> i64 {\n    let mut r: R = R { a: 0, b: 0 };\n    let b: R = r;\n    r.a = 1;\n    let y: i64 = b.b;\n    return 0;\n}\n",
    ),
    // ── SHP-5c-2 twins ──
    // The slots are positional: the callee writes through its second parameter, which is
    // `scratch` here, so `out`'s region stays clean (the reject swaps the arguments).
    (
        "SHP-5c-2 S5 twin — the written-through argument is not the one returned — clean",
        "module tool;\nfn poke(out: i64, scratch: i64) -> i64 {\n    let s: i64 @Secret = 1;\n    store8(scratch, s & 1);\n    return 1;\n}\npub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let scratch: i64 = alloc(8);\n    let n: i64 = poke(out, scratch);\n    return out << 32 | n;\n}\n",
    ),
    // A callee whose own bound is @Public, called at a @Public site, raises nothing — whatever
    // it materialises or stores — even in a program that carries a secret elsewhere.
    (
        "SHP-5c-2 S5 twin — a public callee at a public site floors nothing — clean",
        "#[ring(outer)] module ext;\nfn mk() -> i64 {\n    let a: [i64; 2] = [1, 0];\n    return 0;\n}\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    let z: i64 = mk();\n    let v: i64 = load8(q);\n    return v;\n}\n",
    ),
    (
        "SHP-5c-2 S5 twin — an impl method storing a public byte through self — clean",
        "#[ring(outer)] module ext;\nrecord B { p: i64 }\nimpl B {\n    fn put(self: B) -> i64 {\n        store8(self.p, 7);\n        return 1;\n    }\n}\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let b: B = B { p: alloc(8) };\n    let n: i64 = b.put();\n    let v: i64 = load8(b.p);\n    return v;\n}\n",
    ),
    // S8 twins: a raw-reading callee under public floors returns a public value; a floored typed
    // result bound at its label is no leak.
    (
        "SHP-5c-2 S8 twin — the callee raw-reads under public floors — clean",
        "#[ring(outer)] module ext;\nfn peek(p: i64) -> i64 {\n    let b: i64 = load8(p);\n    return b;\n}\nfn f(s: i64 @Secret) -> i64 ! { Alloc } {\n    let q: i64 = alloc(8);\n    let v: i64 = peek(q);\n    return v;\n}\n",
    ),
    (
        "SHP-5c-2 S8 twin — the floored typed result is bound @Secret — clean",
        "module ext;\nfn helper() -> i64 {\n    let t: str = \"abc\";\n    return t.len();\n}\nfn f(s: i64 @Secret) -> i64 {\n    let mut a: [i64; 2] = [0, 0];\n    a[0] = s;\n    let n: i64 @Secret = helper();\n    return 0;\n}\n",
    ),
    (
        "SHP-5c-2 S5 twin — the slot past the nested call is the buffer not returned — clean",
        "module tool;\nfn id(x: i64) -> i64 {\n    return x;\n}\nfn inner(a: i64, b: i64) -> i64 {\n    let s: i64 @Secret = 1;\n    store8(b, s & 1);\n    return 1;\n}\nfn poke(x: i64, y: i64) -> i64 {\n    return inner(id(y), x);\n}\npub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n    let out: i64 = alloc(64);\n    let scratch: i64 = alloc(8);\n    let n: i64 = poke(scratch, out);\n    return out << 32 | n;\n}\n",
    ),
    // SHP-5c-3 twins: a scalar region body beside a secret, the handle handed to a `Region`
    // parameter, a body-local `let mut` rebound, a public write through an outer record, and
    // a slot round trip beside a secret — clean on both sides.
    (
        "SHP-5c-3 twin — a scalar region body keeps its labels — clean",
        "#[ring(outer)] module ext;\nfn f(secret: i64 @Secret) -> i64 ! { Alloc } {\n    region scratch(64) {\n        let kept: i64 @Secret = secret;\n        let open: i64 = 1;\n    };\n    return 0;\n}\n",
    ),
    (
        "SHP-5c-3 twin — the region handle handed to a Region parameter — clean",
        "#[ring(outer)] module ext;\nfn use_region(r: Region) -> i64 {\n    return 0;\n}\nfn f(secret: i64 @Secret) -> i64 ! { Alloc } {\n    region scratch(64) {\n        let n: i64 = use_region(scratch);\n    };\n    return 0;\n}\n",
    ),
    (
        "SHP-5c-3 twin — a body-local let mut rebound inside the body — clean",
        "#[ring(outer)] module ext;\nfn f(secret: i64 @Secret) -> i64 ! { Alloc } {\n    region scratch(64) {\n        let mut n: i64 = 1;\n        n = n + 1;\n    };\n    return 0;\n}\n",
    ),
    (
        "SHP-5c-3 twin — a public write through an outer record inside the body — clean",
        "#[ring(outer)] module ext;\nrecord P { x: i64 }\nfn f(secret: i64 @Secret) -> i64 ! { Alloc } {\n    let mut p: P = P { x: 0 };\n    region scratch(64) {\n        p.x = 1;\n    };\n    return p.x;\n}\n",
    ),
    (
        "SHP-5c-3 twin — a slot round trip beside a secret — clean",
        "module ext;\ncap type Fuel {}\nfn f(c: Fuel, secret: i64 @Secret) -> Fuel {\n    let s: Slot<Fuel> = slot_new::<Fuel>();\n    slot_put(s, c);\n    let back: Fuel = slot_take(s);\n    return back;\n}\n",
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
        // SHP-5a modelled the control-flow join, so a nonpublic early exit is checked, not
        // refused (`CORPUS_ACCEPT`). A tuple let keeps its all-public projection: a RHS that
        // carries a nonpublic pc is still outside it and fails closed.
        (
            "tuple let under a secret pc",
            "module ext; fn mk() -> (i64, i64) { return (1, 2); } fn f(s: i64 @Secret) -> i64 @Secret { if s > 0 { let (a, b) = mk(); return s; } else { } return s; }",
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
        // SHP-5c-3: a region body is admitted by the scalar-only rule (tt_region_body_scalar),
        // which stands in for production's escape lattice, and refused otherwise: a body
        // binding a record, a str or a slot, or handing a non-scalar to a call. Production
        // accepts each program below.
        (
            "region body binding a record",
            "#[ring(outer)] module ext;\nrecord P { x: i64 }\nfn f(secret: i64 @Secret) -> i64 ! { Alloc } {\n    region scratch(64) {\n        let p: P = P { x: 1 };\n    };\n    return 0;\n}\n",
        ),
        (
            "region body binding a str",
            "#[ring(outer)] module ext;\nfn f(secret: i64 @Secret) -> i64 ! { Alloc } {\n    region scratch(64) {\n        let t: str = \"abc\";\n    };\n    return 0;\n}\n",
        ),
        (
            "region body binding a slot",
            "#[ring(outer)] module ext;\ncap type Fuel {}\nfn f(secret: i64 @Secret) -> i64 ! { Alloc } {\n    region scratch(64) {\n        let s: Slot<Fuel> = slot_new::<Fuel>();\n    };\n    return 0;\n}\n",
        ),
        (
            "region body handing a str to a call",
            "#[ring(outer)] module ext;\nfn len_of(t: str) -> i64 {\n    return t.len();\n}\nfn f(secret: i64 @Secret) -> i64 ! { Alloc } {\n    region scratch(64) {\n        let n: i64 = len_of(\"abc\");\n    };\n    return 0;\n}\n",
        ),
        // SHP-5c-1: the heap floors read a syntactic typing. An alias is not resolved by it (an
        // alias of a scalar typed as a nominal would raise a floor production does not), and a
        // generic record's field is typed by its instance, out of view: both refuse rather than
        // guess — the field only where a non-public label makes the floor rules read it.
        (
            "type alias",
            "module ext; type Id = i64; fn f(x: Id) -> i64 { return 0; }",
        ),
        (
            "generic record field at a secret label",
            "module ext; record Box<T> { v: T } fn f(s: i64 @Secret) -> i64 @Secret { let b: Box<i64> = Box { v: 1 }; if s > 0 { let y: i64 @Secret = b.v; } else { } return s; }",
        ),
        // SHP-5c-2: a call site applies its callee's summary; a callee this shadow cannot name —
        // a stdlib method with no body in view, a routed int method whose stdlib fn depends on
        // the int's width — refuses while a label makes the summaries live.
        (
            "stdlib callee with no body in view while a label is non-public",
            "module ext; fn f(s: i64 @Secret) -> i64 { let v: Vec<i64> = Vec::new(); return 0; }",
        ),
        (
            "int to_string whose stdlib fn depends on the width, beside a secret",
            "module ext; fn f(s: i64 @Secret) -> i64 { let t: str = s.to_string(); return 0; }",
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

/// SHP-5c-2: a site where production applies its program-wide bound — a `grant` of a closure held
/// in a local, an indirect call — refuses while the summaries are live, including in a program
/// whose only non-public label is an effect operation's parameter (the shadow's signal walk reads
/// it off the operation's K_PARAM, like any parameter's label). Each refused program has a twin
/// identical but for the label that makes the summaries live: the oracle accepts it and the
/// shadow checks it with no refusal, so the refusal is the label's, never the shape's alone.
#[test]
fn sh_taint_program_bound_sites_refuse_only_while_live() {
    let pairs = [
        (
            "grant of a closure held in a local, beside a secret",
            "module ext; cap type C {} fn f(c: C, g: Fn(&C) -> i64, s: i64 @Secret) -> i64 { let mut a: [i64; 2] = [0, 0]; let z: i64 = grant(&c, g); let y: i64 = a[0]; return y; }",
            "module ext; cap type C {} fn f(c: C, g: Fn(&C) -> i64, s: i64) -> i64 { let mut a: [i64; 2] = [0, 0]; let z: i64 = grant(&c, g); let y: i64 = a[0]; return y; }",
        ),
        (
            "indirect call where the only label is an effect operation's parameter",
            "#[ring(outer)] module ext; effect Log { fn note(x: i64 @Secret) -> i64; } fn apply(g: Fn(i64) -> i64, p: i64) -> i64 ! { Alloc } { let q: i64 = alloc(8); let r: i64 = g(p); let v: i64 = load8(q); return v; }",
            "#[ring(outer)] module ext; effect Log { fn note(x: i64) -> i64; } fn apply(g: Fn(i64) -> i64, p: i64) -> i64 ! { Alloc } { let q: i64 = alloc(8); let r: i64 = g(p); let v: i64 = load8(q); return v; }",
        ),
    ];
    for (label, refused, twin) in pairs {
        assert_eq!(
            oracle_tcodes(refused),
            vec!["T001".to_string()],
            "SH-TAINT {label}: the program-wide bound floors the later read in the oracle:\n{refused}"
        );
        let output = full_output(refused);
        assert!(
            output.split(';').any(|item| item == TAINT_UNSUPPORTED),
            "SH-TAINT {label}: a program-wide-bound site produced an apparently clean verdict: {output:?}"
        );
        assert!(
            oracle_tcodes(twin).is_empty(),
            "SH-TAINT {label}: the label-free twin must be taint-clean in the oracle:\n{twin}"
        );
        let twin_output = full_output(twin);
        assert!(
            !twin_output.split(';').any(|item| item == TAINT_UNSUPPORTED),
            "SH-TAINT {label}: the label-free twin was refused, so the refusal is not the label's: {twin_output:?}"
        );
        assert!(
            sigil_tcodes(twin).is_empty(),
            "SH-TAINT {label}: the label-free twin carries a spurious T-code: {twin_output:?}"
        );
    }
}

/// A caller of a `@Flow` function: the shadow refuses the flow body (its instances are out of
/// view) and checks the caller against the `@Flow` signature as production resolves it — the
/// argument is accepted at its own label and the call's label is the argument's — so the output
/// carries the refusal and no core T-code, where the oracle is clean. Before SHP-5c-2 the caller
/// read the `@Flow` parameter and return as `@Public` and emitted a false T001 beside the refusal.
#[test]
fn sh_taint_flow_caller_refuses_without_a_false_code() {
    let src = "#[ring(outer)] #[trusted]\nmodule flow_secret_only;\npub fn codec(value: i64 @Flow) -> i64 @Flow { return value; }\nfn secret_caller(value: i64 @Secret) -> i64 @Secret { return codec(value); }\n";
    assert!(
        oracle_tcodes(src).is_empty(),
        "the oracle resolves the @Flow instance at the caller's label and accepts:\n{src}"
    );
    let output = full_output(src);
    assert!(
        output.split(';').any(|item| item == TAINT_UNSUPPORTED),
        "the @Flow body is refused, never silently checked: {output:?}"
    );
    assert!(
        sigil_tcodes(src).is_empty(),
        "a caller of a @Flow function carries a false T-code beside the refusal: {output:?}"
    );
}

/// M6's region masks name at most 62 regions per function; a 63rd `alloc` site is REFUSED
/// (SH_TAINT_UNSUPPORTED), never silently unregioned. 62 sites are still checked exactly
/// (the clean control), so the bound is the only thing this pins.
#[test]
fn sh_taint_region_overflow_is_explicit() {
    let program = |sites: usize| {
        let lets: String = (0..sites)
            .map(|k| format!("    let p{k}: i64 = alloc(8);\n"))
            .collect();
        format!(
            "#[ring(outer)] module ext;\nfn f(s: i64 @Secret) -> i64 ! {{ Alloc }} {{\n{lets}    store8(p0, s);\n    return p0;\n}}\n"
        )
    };
    let within = program(62);
    assert_eq!(oracle_tcodes(&within), vec!["T001".to_string()]);
    assert_eq!(sigil_tcodes(&within), vec!["T001".to_string()]);
    assert!(
        !full_output(&within)
            .split(';')
            .any(|c| c == TAINT_UNSUPPORTED),
        "62 regions are within the mask and must be checked, not refused"
    );
    let beyond = program(63);
    assert!(
        full_output(&beyond)
            .split(';')
            .any(|c| c == TAINT_UNSUPPORTED),
        "a 63rd alloc site must refuse rather than drop a region"
    );
}

// ── SHP-5a property test: the control-flow join over secret and public guards ────────────
//
// The join fixtures are hand-picked; this generates bodies over the whole join surface the
// shadow models — public lets, secret- and public-guarded `if`s with assignments, a one-sided
// `return`, a `while` with a secret-guarded `break`, a `match` on a secret, a range over a
// public bound, a @SecretCT guard (the no-descent rule) — and asserts EXACT agreement: the
// shadow's code set equals the oracle's and nothing is refused. Agreement here is not
// cleanliness: most bodies leak through the pc or the continuation, so the property is that
// both sides see the same leak. Each template is closed over its index so names never collide.
mod joinmodel_prop {
    use super::*;
    use proptest::prelude::*;

    fn block(kind: u8, i: usize) -> String {
        match kind {
            0 => format!("    let a{i}: i64 = p + {i};\n"),
            1 => {
                format!("    if s > {i} {{\n        let b{i}: i64 = {i};\n    }} else {{\n    }}\n")
            }
            2 => format!(
                "    if p > {i} {{\n        let c{i}: i64 @Secret = s;\n    }} else {{\n    }}\n"
            ),
            3 => format!(
                "    let mut w{i}: i64 = 0;\n    while w{i} < 3 {{\n        if s > w{i} {{\n            break;\n        }}\n        w{i} = w{i} + 1;\n    }}\n    let x{i}: i64 = w{i};\n"
            ),
            4 => format!(
                "    let mut v{i}: i64 @Secret = 0;\n    match s {{\n        0 => {{ v{i} = 1; }},\n        _ => {{ v{i} = 2; }},\n    }}\n"
            ),
            5 => format!(
                "    for k{i} in 0..p {{\n        let d{i}: i64 @Secret = s + k{i};\n    }}\n"
            ),
            6 => format!(
                "    let mut m{i}: i64 = p;\n    if s > 0 {{\n        m{i} = 1;\n    }} else {{\n        m{i} = 2;\n    }}\n    let n{i}: i64 = m{i};\n"
            ),
            7 => format!("    if s > {i} {{\n        return s;\n    }} else {{\n    }}\n"),
            _ => {
                format!("    if c == {i} {{\n        let e{i}: i64 = 1;\n    }} else {{\n    }}\n")
            }
        }
    }

    fn program(kinds: &[u8]) -> String {
        let body: String = kinds
            .iter()
            .enumerate()
            .map(|(i, k)| block(*k, i))
            .collect();
        format!(
            "module ext;\nfn f(s: i64 @Secret, p: i64, c: i64 @SecretCT) -> i64 @Secret {{\n{body}    return s;\n}}\n"
        )
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: case_budget(32), ..ProptestConfig::default() })]
        #[test]
        fn joinmodel_surface_agrees_exactly(
            kinds in proptest::collection::vec(0u8..9, 1..7)
        ) {
            let src = program(&kinds);
            let oracle = oracle_tcodes(&src);
            let shadow = sigil_tcodes(&src);
            prop_assert_eq!(&shadow, &oracle, "shadow {:?} vs oracle {:?}:\n{}", shadow, oracle, src);
            let raw = full_output(&src);
            prop_assert!(
                !raw.split(';').any(|c| c == TAINT_UNSUPPORTED),
                "shadow refused a modelled join shape:\n{}\n{}", src, raw
            );
        }
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
        #![proptest_config(ProptestConfig { cases: case_budget(32), ..ProptestConfig::default() })]
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
