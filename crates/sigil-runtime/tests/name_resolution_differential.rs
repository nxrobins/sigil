//! SH-NR-0 — differential parity for the self-hosted structural name-resolver.
//!
//! Composes `selfhost/lexer.sigil` + `parser.sigil` + `name_resolution.sigil` into
//! one tool emitting a `records|pool|diags` stream where each record is
//! `<def_id>,<kind_tag>,<name>;` for the module (DefId 0) then each NAMED top-level
//! item in source order (`use`/`impl` skipped — oracle `name()==None`). Compared
//! field-for-field against the authoritative Rust oracle `name_resolution::resolve`
//! (pinned 452b741). Scope: CLEAN single-module programs (no name errors, no `use`).
//! See `docs/specs/sh-name-resolution.md` for the current boundary.

use sigil_compiler::compile_tool;
use sigil_compiler::name_resolution::{self, ResolvedItemKind};
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");
const NAMERES: &str = include_str!("../../../selfhost/name_resolution.sigil");
const FUEL: u64 = 300_000_000;

/// Strip the per-file `module X;` headers and concatenate into one `module tool;`.
fn nr_tool(body: &str) -> String {
    let lexer_defs = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser_defs = PARSER.replace("\nmodule parser;\n", "\n");
    let nr_defs = NAMERES.replace("\nmodule name_resolution;\n", "\n");
    format!(
        "module tool;\n{lexer_defs}\n{parser_defs}\n{nr_defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// src -> lex -> parse -> nr_encode -> output.
fn nr_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = nr_encode(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

/// Compile the composed tool ONCE.
fn nr_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        compile_tool(&nr_tool(nr_body()))
            .expect("name_resolution tool should compile")
            .wasm
    })
}

/// Run the SIGIL tool and return its records section (before the first `|`).
fn sigil_records(src: &str) -> String {
    let result = execute_ephemeral(nr_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("name_resolution tool executes");
    let text = String::from_utf8(result.output).expect("tool output is UTF-8");
    let (recs, _rest) = text.split_once('|').expect("output has a | separator");
    recs.to_string()
}

fn kind_tag(k: ResolvedItemKind) -> i64 {
    match k {
        ResolvedItemKind::Const => 1,
        ResolvedItemKind::Function => 2,
        ResolvedItemKind::Actor => 3,
        ResolvedItemKind::CapabilityType => 4,
        ResolvedItemKind::Record => 5,
        ResolvedItemKind::Enum => 6,
        ResolvedItemKind::Impl => 7,
    }
}

/// The oracle: parse + `resolve` + serialize to the SAME record format. MUST call
/// the authoritative `name_resolution::resolve` — no parallel re-impl (ET-NR0-8).
fn oracle_records(src: &str) -> String {
    let source = SourceFile::new("<nr-diff>", src);
    let (ast, _diags) = parser::parse(&source);
    let resolved = name_resolution::resolve(&ast).expect("clean corpus must resolve");
    let mut out = String::new();
    for m in &resolved.modules {
        // ET-NR0-7: the SH-NR-0 corpus is `use`-free, so use_scope must be empty.
        assert!(
            m.use_scope.aliases.is_empty(),
            "SH-NR-0 corpus must be `use`-free: {src:?}"
        );
        out.push_str(&format!("{},0,{};", m.def_id.0, m.name));
        for it in &m.items {
            out.push_str(&format!(
                "{},{},{};",
                it.def_id.0,
                kind_tag(it.kind),
                it.name
            ));
        }
    }
    out
}

/// Parse a record stream into (def_id, kind_tag, name) tuples, sorted numerically
/// by `def_id` (ET-NR0-6: no lexical `'10'<'2'` hazard). Each record is exactly 3 fields.
fn parse_recs(records: &str) -> Vec<(u32, i64, String)> {
    let mut v: Vec<(u32, i64, String)> = records
        .split(';')
        .filter(|s| !s.is_empty())
        .map(|r| {
            let parts: Vec<&str> = r.splitn(3, ',').collect();
            assert_eq!(parts.len(), 3, "record must have exactly 3 fields: {r:?}");
            let did: u32 = parts[0].parse().expect("def_id is u32");
            let tag: i64 = parts[1].parse().expect("kind_tag is i64");
            (did, tag, parts[2].to_string())
        })
        .collect();
    v.sort();
    v
}

/// The FROZEN clean single-module corpus (no name errors, no `use`).
const CORPUS: &[&str] = &[
    // one fn -> module(0), fn(1)
    "module m;\npub fn f() -> i64 { return 0; }\n",
    // record + fn -> module(0), record(1), fn(2)
    "module m;\nrecord P { x: i64 }\nfn g() -> i64 { return 0; }\n",
    // const + enum + fn -> module(0), const(1), enum(2), fn(3)
    "module m;\nconst K: i64 = 5;\nenum E { A, B }\nfn h() -> i64 { return 0; }\n",
    // three-fn ordering -> module(0), fn(1), fn(2), fn(3)
    "module m;\nfn a() -> i64 { return 1; }\nfn b() -> i64 { return 2; }\nfn c() -> i64 { return 3; }\n",
    // IMPL-skip proof: impl gets NO DefId, so f is DefId 2 not 3 -> module(0), record(1), fn(2)
    "module m;\nrecord P { x: i64 }\nimpl P { fn get(self: P) -> i64 { return self.x; } }\nfn f() -> i64 { return 0; }\n",
    // cap type + fn -> module(0), captype(1), fn(2)
    "module m;\ncap type Fuel { burn }\nfn f() -> i64 { return 0; }\n",
];

/// DONE-LINE GATE: exact resolution parity (DefId pre-order + name + kind) on the
/// clean corpus.
#[test]
fn sh_nr_0_resolution_matches_oracle() {
    for (i, src) in CORPUS.iter().enumerate() {
        assert_eq!(
            parse_recs(&sigil_records(src)),
            parse_recs(&oracle_records(src)),
            "SH-NR-0 #{i}: self-hosted resolution must match the oracle:\n{src}"
        );
    }
}

/// NON-STUB (ET-NR0-1): >=2 corpus inputs yield >=2 DISTINCT sigil streams, AND a
/// fixed reference input byte-matches the oracle's non-trivial output.
#[test]
fn sh_nr_0_non_stub() {
    let streams: std::collections::BTreeSet<String> =
        CORPUS.iter().map(|s| sigil_records(s)).collect();
    assert!(
        streams.len() >= 2,
        "stub: all {} corpus inputs produced identical streams",
        CORPUS.len()
    );
    let reference = "module m;\nrecord P { x: i64 }\nfn g() -> i64 { return 0; }\n";
    assert_eq!(
        parse_recs(&sigil_records(reference)),
        parse_recs(&oracle_records(reference)),
        "reference input must byte-match the oracle"
    );
    assert_eq!(
        parse_recs(&oracle_records(reference)).len(),
        3,
        "reference oracle output must be non-trivial (module + 2 items)"
    );
}

/// DETERMINISM (ET-NR0-5): two runs of the compiled tool are byte-identical.
#[test]
fn sh_nr_0_deterministic() {
    for src in CORPUS {
        assert_eq!(
            sigil_records(src),
            sigil_records(src),
            "non-deterministic output for: {src}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SH-NR-1 — `use`-scope alias resolution + N007/N009 parity.
// The self-hosted stream is now 4 sections `recs|pool|aliases|diags`; SH-NR-0's
// `sigil_records` (recs, before the first `|`) is unperturbed (ET-NR1-1/2). Clean
// fixtures (resolve→Ok) compare recs + aliases; error fixtures (resolve→Err) compare
// diagnostic CODES only — recs/aliases are unavailable on Err (ET-NR1-10/12).
// ─────────────────────────────────────────────────────────────────────────────

/// Full UTF-8 tool output for `src`.
fn full_output(src: &str) -> String {
    let result = execute_ephemeral(nr_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("name_resolution tool executes");
    String::from_utf8(result.output).expect("tool output is UTF-8")
}

/// Split the output into its `|`-delimited sections (recs, pool, aliases, diags).
fn sigil_sections(src: &str) -> Vec<String> {
    let secs: Vec<String> = full_output(src).split('|').map(|s| s.to_string()).collect();
    assert!(
        secs.len() >= 4,
        "SH-NR-1 output must have 4 sections (recs|pool|aliases|diags): {src:?}"
    );
    secs
}

/// Self-hosted aliases as a sorted-deduped set of (module, target) pairs (ET-NR1-6).
fn sigil_aliases(src: &str) -> Vec<(String, String)> {
    let secs = sigil_sections(src);
    let mut v: Vec<(String, String)> = secs[2]
        .split(';')
        .filter(|s| !s.is_empty())
        .map(|a| {
            let p: Vec<&str> = a.splitn(2, ',').collect();
            assert_eq!(p.len(), 2, "alias must have exactly 2 fields: {a:?}");
            (p[0].to_string(), p[1].to_string())
        })
        .collect();
    v.sort();
    v.dedup();
    v
}

/// Self-hosted diagnostic codes, sorted multiset (ET-NR1-12: codes only).
fn sigil_diags(src: &str) -> Vec<String> {
    let secs = sigil_sections(src);
    let mut v: Vec<String> = secs[3]
        .split(';')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect();
    v.sort();
    v
}

/// Oracle recs for a CLEAN multi-module program (global pre-order; NO use-free
/// assert, unlike SH-NR-0's `oracle_records`). MUST call `resolve` (ET-NR1-13).
fn oracle_recs_multi(src: &str) -> String {
    let source = SourceFile::new("<nr-diff>", src);
    let (ast, _diags) = parser::parse(&source);
    let resolved = name_resolution::resolve(&ast).expect("clean NR1 fixture must resolve");
    let mut out = String::new();
    for m in &resolved.modules {
        out.push_str(&format!("{},0,{};", m.def_id.0, m.name));
        for it in &m.items {
            out.push_str(&format!(
                "{},{},{};",
                it.def_id.0,
                kind_tag(it.kind),
                it.name
            ));
        }
    }
    out
}

/// Oracle aliases as a sorted-deduped (module, target) set (key==value==target).
fn oracle_aliases(src: &str) -> Vec<(String, String)> {
    let source = SourceFile::new("<nr-diff>", src);
    let (ast, _diags) = parser::parse(&source);
    let resolved = name_resolution::resolve(&ast).expect("clean NR1 fixture must resolve");
    let mut v: Vec<(String, String)> = Vec::new();
    for m in &resolved.modules {
        for target in m.use_scope.aliases.values() {
            v.push((m.name.clone(), target.clone()));
        }
    }
    v.sort();
    v.dedup();
    v
}

/// Oracle diagnostic codes (sorted). `resolve` returns Err on any N-code; an Ok
/// program has none. MUST call `resolve` (ET-NR1-13).
fn oracle_diags(src: &str) -> Vec<String> {
    let source = SourceFile::new("<nr-diff>", src);
    let (ast, _diags) = parser::parse(&source);
    let mut v: Vec<String> = match name_resolution::resolve(&ast) {
        Ok(_) => Vec::new(),
        Err(ds) => ds.iter().map(|d| d.code().to_string()).collect(),
    };
    v.sort();
    v
}

/// CLEAN multi-module `use`-bearing corpus (resolve→Ok: compare recs + aliases).
const CORPUS_NR1_CLEAN: &[&str] = &[
    // a uses b -> recs a0 f1 b2 g3; alias (a,b).
    "module a;\nuse b;\nfn f() -> i64 { return 0; }\nmodule b;\nfn g() -> i64 { return 1; }\n",
    // chain a->b->c (no cycle) -> aliases (a,b),(b,c).
    "module a;\nuse b;\nfn f() -> i64 { return 0; }\nmodule b;\nuse c;\nfn g() -> i64 { return 1; }\nmodule c;\nfn h() -> i64 { return 2; }\n",
    // 2-segment `use crate::b;` -> alias (a,b) (proves last-segment extraction).
    "module a;\nuse crate::b;\nfn f() -> i64 { return 0; }\nmodule b;\nfn g() -> i64 { return 1; }\n",
    // diamond a->c, b->c (no cycle) -> aliases (a,c),(b,c).
    "module a;\nuse c;\nfn f() -> i64 { return 0; }\nmodule b;\nuse c;\nfn g() -> i64 { return 1; }\nmodule c;\nfn h() -> i64 { return 2; }\n",
];

/// ERROR corpus (resolve→Err: compare diagnostic CODES only — ET-NR1-10).
const CORPUS_NR1_ERR: &[&str] = &[
    // N007 unresolved use.
    "module a;\nuse missing;\nfn f() -> i64 { return 0; }\nmodule b;\nfn g() -> i64 { return 1; }\n",
    // N007 self-use.
    "module a;\nuse a;\nfn f() -> i64 { return 0; }\nmodule b;\nfn g() -> i64 { return 1; }\n",
    // N007 unsupported path shape (>=3 segments).
    "module a;\nuse x::y::z;\nfn f() -> i64 { return 0; }\nmodule b;\nfn g() -> i64 { return 1; }\n",
    // N009 two-module cycle a<->b.
    "module a;\nuse b;\nfn f() -> i64 { return 0; }\nmodule b;\nuse a;\nfn g() -> i64 { return 1; }\n",
    // N009 three-module cycle a->b->c->a.
    "module a;\nuse b;\nfn f() -> i64 { return 0; }\nmodule b;\nuse c;\nfn g() -> i64 { return 1; }\nmodule c;\nuse a;\nfn h() -> i64 { return 2; }\n",
];

/// DONE-LINE GATE (clean half): every `use`-aliased module resolves to the correct
/// target; recs + aliases match the oracle; zero diagnostics.
#[test]
fn sh_nr_1_clean_resolution_matches_oracle() {
    for (i, src) in CORPUS_NR1_CLEAN.iter().enumerate() {
        assert_eq!(
            parse_recs(&sigil_records(src)),
            parse_recs(&oracle_recs_multi(src)),
            "SH-NR-1 clean #{i}: recs must match the oracle:\n{src}"
        );
        assert_eq!(
            sigil_aliases(src),
            oracle_aliases(src),
            "SH-NR-1 clean #{i}: use-scope aliases must match the oracle:\n{src}"
        );
        assert!(
            sigil_diags(src).is_empty(),
            "SH-NR-1 clean #{i}: clean fixture must emit no diagnostics:\n{src}"
        );
    }
}

/// DONE-LINE GATE (error half): {N007, N009} at exact-match parity; 0 false-accepts.
#[test]
fn sh_nr_1_use_errors_match_oracle() {
    for (i, src) in CORPUS_NR1_ERR.iter().enumerate() {
        let oracle = oracle_diags(src);
        assert!(
            !oracle.is_empty(),
            "SH-NR-1 error #{i}: fixture must actually error in the oracle:\n{src}"
        );
        assert_eq!(
            sigil_diags(src),
            oracle,
            "SH-NR-1 error #{i}: diagnostic codes must match the oracle:\n{src}"
        );
    }
}

/// NON-STUB (ET-NR1-14): >=2 distinct full streams + a clean reference whose recs
/// AND aliases byte-match the oracle (with a non-trivial alias).
#[test]
fn sh_nr_1_non_stub() {
    let mut all: Vec<&str> = Vec::new();
    all.extend_from_slice(CORPUS_NR1_CLEAN);
    all.extend_from_slice(CORPUS_NR1_ERR);
    let streams: std::collections::BTreeSet<String> = all.iter().map(|s| full_output(s)).collect();
    assert!(
        streams.len() >= 2,
        "stub: all SH-NR-1 fixtures produced identical streams"
    );
    let reference = CORPUS_NR1_CLEAN[0];
    assert_eq!(
        parse_recs(&sigil_records(reference)),
        parse_recs(&oracle_recs_multi(reference)),
        "reference recs must byte-match the oracle"
    );
    assert_eq!(
        sigil_aliases(reference),
        oracle_aliases(reference),
        "reference aliases must byte-match the oracle"
    );
    assert_eq!(
        oracle_aliases(reference).len(),
        1,
        "reference oracle aliases must be non-trivial (exactly one resolved use)"
    );
}

/// DETERMINISM (ET-NR1-15): two runs of the compiled tool are byte-identical.
#[test]
fn sh_nr_1_deterministic() {
    let mut all: Vec<&str> = Vec::new();
    all.extend_from_slice(CORPUS_NR1_CLEAN);
    all.extend_from_slice(CORPUS_NR1_ERR);
    for src in all {
        assert_eq!(
            full_output(src),
            full_output(src),
            "non-deterministic: {src}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// SH-NR-2 — collision/validity diagnostics + DefId-injectivity + full-stdlib parity
// Error fixtures (resolve→Err) compare diagnostic codes only
// (ET-NR2-3); clean fixtures + the 23 stdlib files compare recs + injectivity.
// ─────────────────────────────────────────────────────────────────────────────

/// ET-NR2-11: assert the recs DefId stream is injective — ids 0..=max each exactly once.
fn assert_injective(recs: &[(u32, i64, String)], label: &str) {
    assert!(!recs.is_empty(), "{label}: empty recs stream");
    let max = recs.iter().map(|(d, _, _)| *d).max().unwrap();
    assert_eq!(
        recs.len() as u32,
        max + 1,
        "{label}: DefId stream not contiguous 0..={max} (len {})",
        recs.len()
    );
    let mut ids: Vec<u32> = recs.iter().map(|(d, _, _)| *d).collect();
    ids.sort_unstable();
    ids.dedup();
    assert_eq!(
        ids.len(),
        recs.len(),
        "{label}: duplicate DefId in the recs stream"
    );
}

/// Enumerate `stdlib/sigil/*.sigil` (mirrors `parser_differential::differential_stdlib_corpus`).
fn stdlib_files() -> Vec<std::path::PathBuf> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/sigil");
    let mut files: Vec<std::path::PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read stdlib dir {}: {e}", dir.display()))
        .map(|e| e.expect("dir entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "sigil"))
        .collect();
    files.sort();
    files
}

/// FULL-STDLIB PARITY (ET-NR2-10): every stdlib file is clean (zero diags both sides),
/// its recs match the oracle, and its DefId stream is injective.
#[test]
fn sh_nr_2_stdlib_corpus_parity() {
    let files = stdlib_files();
    assert!(
        files.len() >= 20,
        "expected >=20 stdlib files, got {}",
        files.len()
    );
    for path in &files {
        let src = std::fs::read_to_string(path).expect("read stdlib file");
        let label = path.display().to_string();
        assert!(
            oracle_diags(&src).is_empty(),
            "{label}: stdlib file must be clean (oracle emitted diagnostics)"
        );
        assert!(
            sigil_diags(&src).is_empty(),
            "{label}: self-hosted emitted spurious diagnostics on a clean stdlib file"
        );
        let sigil = parse_recs(&sigil_records(&src));
        let oracle = parse_recs(&oracle_recs_multi(&src));
        assert_eq!(sigil, oracle, "{label}: stdlib recs must match the oracle");
        assert_injective(&sigil, &label);
    }
}

/// SH-NR-2 collision/validity error corpus — one ISOLATED code per fixture.
/// N012 (case-collision) is ORACLE DEAD CODE: a valid module name matches
/// `^[a-z_][a-z0-9_]*$` (lowercase only), so two VALID names cannot differ only in
/// case — an uppercase name is rejected by N011 first (which `continue`s). It is
/// therefore unreachable and proven so by `sh_nr_2_n012_unreachable` below, not by
/// an isolating fixture. So the reachable error corpus holds 7 codes.
const CORPUS_NR2_ERR: &[(&str, &str)] = &[
    ("N011", "module Bad;\nfn f() -> i64 { return 0; }\n"),
    (
        "N001",
        "module a;\nfn f() -> i64 { return 0; }\nmodule a;\nfn g() -> i64 { return 1; }\n",
    ),
    (
        "N002",
        "module a;\nfn f() -> i64 { return 0; }\nfn f() -> i64 { return 1; }\n",
    ),
    (
        "N005",
        "module a;\nfn f(x: i64, x: i64) -> i64 { return x; }\n",
    ),
    (
        "N003",
        "module a;\nactor Counter {\n    state { n: i64 }\n    on ping(x: i64) -> i64 { return x; }\n    on ping(y: i64) -> i64 { return y; }\n}\n",
    ),
    (
        "N004",
        "module a;\nactor Counter {\n    state { n: i64, n: i64 }\n    on ping(x: i64) -> i64 { return x; }\n}\n",
    ),
    (
        "N006",
        "module a;\nactor Counter {\n    state { n: i64 }\n    on ping(n: i64) -> i64 { return n; }\n}\n",
    ),
];

/// DONE-LINE GATE: {N001,N002,N003,N004,N005,N006,N011,N012} at exact-match parity;
/// each fixture isolates exactly one code (ET-NR2-14).
#[test]
fn sh_nr_2_collision_errors_match_oracle() {
    assert_eq!(
        CORPUS_NR2_ERR.len(),
        7,
        "expected 7 isolated reachable-code fixtures (N012 is unreachable)"
    );
    let distinct: std::collections::BTreeSet<&str> =
        CORPUS_NR2_ERR.iter().map(|(c, _)| *c).collect();
    assert_eq!(
        distinct.len(),
        7,
        "the 7 fixtures must cover 7 distinct reachable codes"
    );
    for (code, src) in CORPUS_NR2_ERR {
        let oracle = oracle_diags(src);
        assert_eq!(
            oracle,
            vec![code.to_string()],
            "SH-NR-2 {code}: the fixture must isolate exactly {code} in the oracle:\n{src}"
        );
        assert_eq!(
            sigil_diags(src),
            oracle,
            "SH-NR-2 {code}: self-hosted diag codes must match the oracle:\n{src}"
        );
    }
}

/// N012 is oracle DEAD CODE: a case-collision input (`module fs; … module Fs;`)
/// yields N011 on the uppercase `Fs` (invalid name, checked first) — NOT N012 —
/// on BOTH sides. This proves the N011-precedence parity and that the self-hosted
/// N012 check (nr_eq_ci, after N011) never spuriously fires (ET-NR2-5 ordering).
#[test]
fn sh_nr_2_n012_unreachable() {
    let src = "module fs;\nfn f() -> i64 { return 0; }\nmodule Fs;\nfn g() -> i64 { return 1; }\n";
    let oracle = oracle_diags(src);
    assert_eq!(
        oracle,
        vec!["N011".to_string()],
        "a would-be case-collision must yield N011 (not N012) in the oracle"
    );
    assert_eq!(
        sigil_diags(src),
        oracle,
        "self-hosted must also emit N011 (not a spurious N012) on:\n{src}"
    );
}

/// The clean SH-NR-1 multi-module fixtures also have injective DefId streams.
#[test]
fn sh_nr_2_clean_fixtures_injective() {
    for src in CORPUS_NR1_CLEAN {
        let recs = parse_recs(&oracle_recs_multi(src));
        assert_injective(&recs, src);
        assert_eq!(
            parse_recs(&sigil_records(src)),
            recs,
            "recs must match the oracle: {src}"
        );
    }
}
