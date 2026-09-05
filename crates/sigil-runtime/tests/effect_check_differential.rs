//! SH-EFFECT — differential parity for the self-hosted effect-row checker.
//!
//! Composes `selfhost/lexer.sigil` + `parser.sigil` + `typecheck.sigil` +
//! `effect_check.sigil` into one tool emitting a `;`-joined E-code stream, compared as a
//! sorted-deduped SET against the authoritative Rust oracle `effect_check::check_effects`
//! run over the full pipeline (`parse → resolve → check_with_options → check_effects`,
//! oracle pinned blob 87f7d82c @10ee9ad). MIN_COVERED = {E001, E002}. The oracle MUST be
//! called directly — no parallel re-impl. See `docs/specs/sh-security-checkers.md`.
//!
//! KEY PARITY FACT (the registration filter): an effect NAME is "registered" iff built-in
//! (FFI/Unsafe) or declared `effect Name;`. The oracle DROPS unregistered names from every
//! row (mod.rs:866) and `alloc` E001 fires only when `Alloc` is registered. The self-host
//! replicates this; the corpus exercises both the registered (E001 fires) and the
//! unregistered-drop (clean) shapes.

use sigil_compiler::CompileOptions;
use sigil_compiler::compile_tool;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{effect_check, name_resolution, type_check};
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");
const TYPECHECK: &str = include_str!("../../../selfhost/typecheck.sigil");
const EFFECTCHECK: &str = include_str!("../../../selfhost/effect_check.sigil");
const FUEL: u64 = 300_000_000;

/// The in-core E-code surface. Both sides filter to this set so the composed typecheck's
/// T-codes can never pollute the comparison (the ET-R7 analog).
const CORE_E_CODES: &[&str] = &["E001", "E002"];

/// Strip the per-file `module X;` headers and concatenate into one `module tool;`.
fn ec_tool(body: &str) -> String {
    let lexer_defs = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser_defs = PARSER.replace("\nmodule parser;\n", "\n");
    let tc_defs = TYPECHECK.replace("\nmodule typecheck;\n", "\n");
    let ec_defs = EFFECTCHECK.replace("\nmodule effect_check;\n", "\n");
    format!(
        "module tool;\n{lexer_defs}\n{parser_defs}\n{tc_defs}\n{ec_defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// src -> lex -> parse -> ec_encode -> output.
fn ec_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = ec_encode(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

/// Compile the composed tool ONCE.
fn ec_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        compile_tool(&ec_tool(ec_body()))
            .expect("effect_check tool should compile")
            .wasm
    })
}

/// Full UTF-8 tool output for `src`.
fn full_output(src: &str) -> String {
    let result = execute_ephemeral(ec_wasm(), src.as_bytes(), FUEL, &IoGrants::none())
        .expect("effect_check tool executes");
    String::from_utf8(result.output).expect("tool output is UTF-8")
}

/// The self-hosted E-codes as a sorted-deduped set, filtered to CORE_E_CODES.
fn sigil_ecodes(src: &str) -> Vec<String> {
    let mut v: Vec<String> = full_output(src)
        .split(';')
        .filter(|s| !s.is_empty())
        .filter(|s| CORE_E_CODES.contains(s))
        .map(|s| s.to_string())
        .collect();
    v.sort();
    v.dedup();
    v
}

/// The oracle's E-codes as a sorted-deduped set, filtered to CORE_E_CODES. MUST call the
/// authoritative `effect_check::check_effects` over the real pipeline.
fn oracle_ecodes(src: &str) -> Vec<String> {
    let source = SourceFile::new("<ec-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    // The corpus is parse-clean (the AG-R7 analog): a parse-erroring fixture would let the
    // oracle "recover" by dropping items and pass vacuously while the self-host parses it
    // differently — a false parity. Reject it here.
    assert!(
        pdiags.is_empty(),
        "SH-EFFECT fixture must be parse-clean: {src:?} -> {:?}",
        pdiags
            .iter()
            .map(|d| d.code().to_string())
            .collect::<Vec<_>>()
    );
    let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
    let (typed, _reg) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .expect("fixture must type-check (the corpus is type-clean)");
    let mut v: Vec<String> = match effect_check::check_effects(&typed) {
        Ok(_) => Vec::new(),
        Err(ds) => ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| CORE_E_CODES.contains(&c.as_str()))
            .collect(),
    };
    v.sort();
    v.dedup();
    v
}

// ─────────────────────────────────────────────────────────────────────────────
// Corpus (all type-clean; every oracle E-code arises from an in-core shape). Each fixture's
// expected deduped E-set is pinned, and `oracle_ecodes` re-derives it from the live oracle
// so the pin and the oracle never drift.
// ─────────────────────────────────────────────────────────────────────────────

/// REJECT fixtures: (label, src, expected sorted-deduped E-set).
const CORPUS_REJECT: &[(&str, &str, &[&str])] = &[
    // E001 — a same-module bare call to a fn requiring a REGISTERED custom effect the caller
    // lacks (the cleanest single-violation E001 shape; `effect NetIO;` registers NetIO).
    (
        "E001 call-leak (registered NetIO)",
        "#[ring(outer)]\nmodule m;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} { return expensive(); }\n",
        &["E001"],
    ),
    // E001 — via the BUILT-IN effect FFI (no `effect` decl needed; FFI is always registered).
    (
        "E001 call-leak (built-in FFI)",
        "#[ring(outer)]\nmodule m;\nfn risky() -> i64 ! { FFI } { return 0; }\nfn boot() -> i64 ! {} { return risky(); }\n",
        &["E001"],
    ),
    // E001 — the `alloc` intrinsic in a no-Alloc fn, with `Alloc` registered via `effect Alloc;`
    // (the alloc-intrinsic trigger; without the decl, Alloc is unregistered and clean — see accept).
    (
        "E001 alloc intrinsic (registered Alloc)",
        "#[ring(outer)]\nmodule m;\neffect Alloc;\nfn f() -> i64 ! {} { let p: i64 = alloc(8); return p; }\n",
        &["E001"],
    ),
    // E001 — the leak is NESTED in an index expression (ET-EFF-3: the walk descends every child,
    // not just statement-position calls).
    (
        "E001 leak in index position (ET-EFF-3)",
        "#[ring(outer)]\nmodule m;\neffect NetIO;\nfn idx() -> i64 ! { NetIO } { return 0; }\nfn boot(arr: [i64; 8]) -> i64 ! {} { let y: i64 = arr[idx()]; return y; }\n",
        &["E001"],
    ),
    // E001 — a leak in a SIBLING statement after a `handle NetIO { … }` block (ET-EFF-7: the
    // handle expansion reverts; statements after it see only the unexpanded set).
    (
        "E001 leak after handle (ET-EFF-7 revert)",
        "#[ring(outer)]\nmodule m;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} {\n    handle NetIO {\n        let a: i64 = expensive();\n    };\n    let b: i64 = expensive();\n    return 0;\n}\n",
        &["E001"],
    ),
    // E002 — `handle Unsafe { … }` in an outer NON-trusted module.
    (
        "E002 untrusted handle Unsafe (outer)",
        "#[ring(outer)]\nmodule m;\nfn f() -> i64 {\n    handle Unsafe {\n        let _x: i64 = 1;\n    };\n    return 0;\n}\n",
        &["E002"],
    ),
    // Multi-module: outer module a leaks NetIO (E001) + outer module b has an untrusted handle
    // Unsafe (E002) — proves per-module ring/trusted dispatch + the program-wide registered set.
    (
        "multi-module E001 (a) + E002 (b)",
        "#[ring(outer)]\nmodule a;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} { return expensive(); }\n#[ring(outer)]\nmodule b;\nfn f() -> i64 {\n    handle Unsafe {\n        let _x: i64 = 1;\n    };\n    return 0;\n}\n",
        &["E001", "E002"],
    ),
];

/// ACCEPT fixtures (CLEAN — no in-core E-code on either side).
const CORPUS_ACCEPT: &[(&str, &str)] = &[
    // The registration filter: NetIO is UNregistered (no `effect` decl), so the `! { NetIO }`
    // row drops to EMPTY → the call leaks nothing → clean. (Without this filter the self-host
    // would false-fire E001 — the load-bearing soundness fixture.)
    (
        "registration filter: unregistered NetIO drops → clean",
        "#[ring(outer)]\nmodule m;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} { return expensive(); }\n",
    ),
    // E001 accept twin: the caller declares NetIO too → the callee row is a subset → clean.
    (
        "E001 accept: caller declares NetIO",
        "#[ring(outer)]\nmodule m;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! { NetIO } { return expensive(); }\n",
    ),
    // alloc accept twin: `effect Alloc;` registers Alloc AND the caller declares it → clean.
    (
        "alloc accept: caller declares Alloc",
        "#[ring(outer)]\nmodule m;\neffect Alloc;\nfn f() -> i64 ! { Alloc } { let p: i64 = alloc(8); return p; }\n",
    ),
    // E002 accept twin: a #[trusted] module may handle Unsafe → clean.
    (
        "E002 accept: trusted handle Unsafe",
        "#[ring(outer)] #[trusted]\nmodule m;\nfn f() -> i64 {\n    handle Unsafe {\n        let _x: i64 = 1;\n    };\n    return 0;\n}\n",
    ),
    // handle-expansion: a `handle NetIO { … }` clears the E001 from a NetIO-requiring call
    // inside it (the lexical expansion).
    (
        "handle-expansion clears the call (clean)",
        "#[ring(outer)]\nmodule m;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} {\n    handle NetIO {\n        let r: i64 = expensive();\n    };\n    return 0;\n}\n",
    ),
    // ET-EFF-5: an INNER module (default ring) with a NetIO leak is SKIPPED wholesale → clean.
    (
        "inner module leak skipped (ET-EFF-5)",
        "module m;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} { return expensive(); }\n",
    ),
    // ET-EFF-5: a `pub` module (flags=4, ring bit 0 = 0) is STILL inner → skipped → clean. A
    // `flags != 0` truthiness misread would (wrongly) treat it as outer and fire E001.
    (
        "pub-inner leak skipped (ET-EFF-5 bit-0)",
        "pub module m;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} { return expensive(); }\n",
    ),
    // ET-EFF-1: an outer fn (no declared row) calling an EXTERN never fires E001 — externs are
    // not subset-checked. Without the extern handling the self-host would false-fire (the
    // extern's {FFI} row ⊄ {}). The extern is in the SEPARATE extern set, not the sig table.
    (
        "extern call never leaks (ET-EFF-1)",
        "#[ring(outer)]\nmodule m;\nextern \"C\" fn ext_fn() -> i64 ! { FFI, Unsafe };\nfn f() -> i64 { return ext_fn(); }\n",
    ),
    // An all-clean outer program (no effects anywhere).
    (
        "all-clean outer program",
        "#[ring(outer)]\nmodule m;\nfn f() -> i64 { return 0; }\nfn g() -> i64 { return f(); }\n",
    ),
    // Cap-expr leaf (found by the adversarial sweep): the oracle treats CapRestrict/CapSplit/
    // CapDraw as LEAVES and does NOT descend into the amount subtree. A leaking call INSIDE a
    // `c.draw(amt())` amount must therefore be CLEAN on both sides — the self-host treats the
    // cap-expr node as a leaf (ec_is_leaf). Without that, ec_scan descended and false-fired E001.
    (
        "cap-draw amount leak is a leaf — clean (adversarial sweep guard)",
        "#[ring(outer)]\nmodule m;\neffect NetIO;\ncap type Fuel { burn }\nfn amt() -> i64 ! { NetIO } { return 1; }\nfn boot(c: Fuel) -> i64 ! {} { let n: Fuel = c.draw(amt()); return 0; }\n",
    ),
    // AG-EFF-8: an UNCALLED generic fn with a registered effect row is CLEAN on both sides —
    // the oracle never monomorphizes it (no instance reaches check_effects) and the self-host
    // skips generic-source fns (ec_is_generic_fn). Without the skip the self-host could
    // false-fire / mis-seed.
    (
        "uncalled generic effect fn skipped (AG-EFF-8)",
        "#[ring(outer)]\nmodule m;\neffect NetIO;\nfn helper<T>(x: T) -> i64 ! { NetIO } { return 0; }\nfn real() -> i64 { return 0; }\n",
    ),
];

/// DONE-LINE GATE (reject half): every reject fixture reproduces the oracle's E-code set
/// exactly, AND that set equals the pinned expectation (so the pin can never silently drift
/// from the oracle).
#[test]
fn sh_effect_reject_matches_oracle() {
    for (label, src, expected) in CORPUS_REJECT {
        let oracle = oracle_ecodes(src);
        let exp: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        assert_eq!(
            oracle, exp,
            "SH-EFFECT {label}: the oracle must emit the pinned E-set:\n{src}"
        );
        assert_eq!(
            sigil_ecodes(src),
            oracle,
            "SH-EFFECT {label}: self-hosted E-codes must match the oracle:\n{src}"
        );
    }
}

/// DONE-LINE GATE (accept half): every accept fixture is CLEAN on both sides (0 in-core
/// E-codes) — the no-false-positive / soundness floor.
#[test]
fn sh_effect_accept_is_clean_both_sides() {
    for (label, src) in CORPUS_ACCEPT {
        assert!(
            oracle_ecodes(src).is_empty(),
            "SH-EFFECT {label}: the accept fixture must be effect-clean in the oracle:\n{src}"
        );
        assert!(
            sigil_ecodes(src).is_empty(),
            "SH-EFFECT {label}: self-hosted emitted a spurious E-code on a clean fixture:\n{src}"
        );
    }
}

/// SOUNDNESS SUBSET: on EVERY fixture (reject ∪ accept), the self-hosted E-set is a SUBSET of
/// the oracle's — never a false E-code (which would reject valid code). On the in-core corpus
/// the two gates above also assert exact equality.
#[test]
fn sh_effect_no_false_ecode_subset() {
    let all = CORPUS_REJECT
        .iter()
        .map(|(l, s, _)| (*l, *s))
        .chain(CORPUS_ACCEPT.iter().copied());
    for (label, src) in all {
        let oracle = oracle_ecodes(src);
        for code in sigil_ecodes(src) {
            assert!(
                oracle.contains(&code),
                "SH-EFFECT {label}: self-hosted emitted {code} not in the oracle set {oracle:?}:\n{src}"
            );
        }
    }
}

/// NON-STUB: a REAL E001 and a REAL E002 each fire on both sides, and >=2 distinct full
/// streams exist (a stub that emits "" everywhere, or a constant, fails here).
#[test]
fn sh_effect_non_stub() {
    let e001 = "#[ring(outer)]\nmodule m;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} { return expensive(); }\n";
    let e002 = "#[ring(outer)]\nmodule m;\nfn f() -> i64 {\n    handle Unsafe {\n        let _x: i64 = 1;\n    };\n    return 0;\n}\n";
    assert_eq!(
        sigil_ecodes(e001),
        vec!["E001".to_string()],
        "E001 must fire"
    );
    assert_eq!(oracle_ecodes(e001), vec!["E001".to_string()], "E001 oracle");
    assert_eq!(
        sigil_ecodes(e002),
        vec!["E002".to_string()],
        "E002 must fire"
    );
    assert_eq!(oracle_ecodes(e002), vec!["E002".to_string()], "E002 oracle");

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

/// DETERMINISM: two runs of the compiled tool are byte-identical.
#[test]
fn sh_effect_deterministic() {
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

/// The oracle path on a STANDALONE file. `Some(codes)` if the file type-checks in isolation
/// (the oracle reaches `check_effects`); `None` if it is dep-blocked.
fn oracle_ecodes_standalone(src: &str) -> Option<Vec<String>> {
    let source = SourceFile::new("<stdlib>", src);
    let (ast, pdiags) = parser::parse(&source);
    if !pdiags.is_empty() {
        return None;
    }
    let resolved = name_resolution::resolve(&ast).ok()?;
    let (typed, _reg) =
        type_check::check_with_options(&resolved, &CompileOptions::default()).ok()?;
    let mut v: Vec<String> = match effect_check::check_effects(&typed) {
        Ok(_) => Vec::new(),
        Err(ds) => ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| CORE_E_CODES.contains(&c.as_str()))
            .collect(),
    };
    v.sort();
    v.dedup();
    Some(v)
}

/// WHOLE-STDLIB effect-clean gate. For every `stdlib/sigil/*.sigil`, auto-partition on whether
/// the oracle can run standalone:
///  - **type-checks standalone** → the self-hosted E-codes EXACTLY match the oracle's (full
///    parity). The stdlib is effect-clean, so both are empty — and this branch includes the
///    effect-ANNOTATED FFI files (extern `! { … }` rows), exercising the extern + row threading
///    at real parity.
///  - **dep-blocked** → the self-hosted tool emits ZERO E-codes (a no-false-positive floor on
///    the real records / closures / generics surface the oracle cannot reach standalone).
#[test]
fn sh_effect_stdlib_clean_parity_and_floor() {
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
        let sig = sigil_ecodes(&src);
        match oracle_ecodes_standalone(&src) {
            Some(oracle) => {
                assert_eq!(
                    sig, oracle,
                    "SH-EFFECT stdlib {name}: self-hosted E-codes must match the oracle"
                );
                parity_files.push(name);
            }
            None => {
                assert!(
                    sig.is_empty(),
                    "SH-EFFECT stdlib {name}: self-hosted emitted a spurious E-code {sig:?} on a (dep-blocked) clean stdlib file"
                );
                floor_files.push(name);
            }
        }
    }

    // Non-stub / non-vacuous: the oracle-parity branch must be substantial.
    assert!(
        parity_files.len() >= 8,
        "stdlib oracle-parity branch is vacuously small ({}): {parity_files:?}",
        parity_files.len()
    );
    // Sanity: the floor branch is also exercised (the dep-blocked surface).
    assert!(
        !floor_files.is_empty(),
        "expected some dep-blocked stdlib files in the no-false-positive floor branch"
    );
}
