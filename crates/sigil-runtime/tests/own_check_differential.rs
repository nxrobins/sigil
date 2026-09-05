//! SH-OWN — differential parity for the self-hosted ownership shadow.
//!
//! The oracle is `ownership::verify(&AirProgram)` (structural, Z3-free, post-capability/pre-memory):
//! CFG-propagated move tracking emitting O001 (use-after-move / duplicate linear use) and O007
//! (move-while-borrowed; O006 is unreachable armor — region escape is caught by T254 first). This
//! lane clones the ring/cap harness: compose lexer+parser+typecheck+own_check into a tool, compare
//! a `;`-joined O-code stream against the oracle over a straight-line, cap-only, type-clean corpus.
//!
//! OWN-0 is the oracle rig + Phase-0 pins (no selfhost code yet). These pins ARE the ground truth
//! the OWN-1/2 shadow will be diffed against.

use sigil_compiler::CompileOptions;
use sigil_compiler::air;
use sigil_compiler::compile_tool;
use sigil_compiler::name_resolution;
use sigil_compiler::ownership;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use sigil_compiler::type_check;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");
const TYPECHECK: &str = include_str!("../../../selfhost/typecheck.sigil");
const OWNCHECK: &str = include_str!("../../../selfhost/own_check.sigil");
const OWN_FUEL: u64 = 300_000_000;

/// The oracle's ordered O-code list for a fixture (program order, filtered to {O001, O007}). Panics
/// (naming the fixture) if it doesn't reach ownership parse+resolve+type-clean — the corpus
/// contract (ET-R7).
fn own_oracle_codes(label: &str, src: &str) -> Vec<String> {
    let source = SourceFile::new("<own-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(
        pdiags.is_empty(),
        "SH-OWN {label}: fixture must be parse-clean, got {:?}\n{src}",
        pdiags
            .iter()
            .map(|d| d.code().to_string())
            .collect::<Vec<_>>()
    );
    let resolved = name_resolution::resolve(&ast)
        .unwrap_or_else(|e| panic!("SH-OWN {label}: fixture must resolve, got {e:?}\n{src}"));
    let (typed, _reg) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .unwrap_or_else(|e| {
            panic!(
                "SH-OWN {label}: fixture must type-check (ET-R7), got {:?}\n{src}",
                e.iter().map(|d| d.code().to_string()).collect::<Vec<_>>()
            )
        });
    let lowered = air::lower(&typed);
    match ownership::verify(&lowered) {
        Ok(_) => Vec::new(),
        Err(ds) => ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| c == "O001" || c == "O007")
            .collect(),
    }
}

/// The OWN-0 pinned corpus: (label, fixture, expected ordered O-code list). Every fixture is
/// straight-line + cap-only + parse+type-clean. Pin provenance (Phase-0 probe, 2026-07-07 —
/// grounded in ownership.rs `apply_moves` / the consuming-site census / CFG state propagation):
/// - MOVE sites fire O001 on the second consuming use: Call (`call_twice`), Spawn (`double_spawn`,
///   the attack_01 shape), CapRestrict (`restrict_then_use`), Send (`send_twice` — the cap IS
///   tracked through the message ctor);
/// - USE-CHECK-ONLY sites: Return sees a prior move (`return_after_move` → O001), but CapDraw is
///   NOT a move (`draw_twice` → clean — draw has no `apply_moves` arm);
/// - O007 (move-while-borrowed) is checked at every modeled consuming site.
const OWN_CORPUS: &[(&str, &str, &[&str])] = &[
    (
        "o001_double_spawn",
        "module sigil;\ncap type Fuel {}\nactor Worker { init(f: Fuel) {} on Ping() -> i64 { return 0; } }\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { let c = fuel.split(50); let a = spawn::<Worker>(c); let b = spawn::<Worker>(c); return 1; }\n}\n",
        &["O001"],
    ),
    (
        "accept_single_spawn",
        "module sigil;\ncap type Fuel {}\nactor Worker { init(f: Fuel) {} on Ping() -> i64 { return 0; } }\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { let c = fuel.split(50); let a = spawn::<Worker>(c); return 1; }\n}\n",
        &[],
    ),
    (
        "call_twice",
        "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a = need(f); let b = need(f); return a; }\n",
        &["O001"],
    ),
    (
        "accept_call_once",
        "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { return need(f); }\n",
        &[],
    ),
    (
        "restrict_then_use",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r = f.restrict(burn); let b = need(f); return b; }\n",
        &["O001"],
    ),
    (
        "draw_twice",
        "module sigil;\ncap type Fuel { burn, query }\nfn go(f: Fuel) -> i64 { let a = f.draw(10); let b = f.draw(20); return 1; }\n",
        &[],
    ),
    (
        "return_after_move",
        "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> Fuel { let a = need(f); return f; }\n",
        &["O001"],
    ),
    (
        "accept_return_only",
        "module sigil;\ncap type Fuel {}\nfn go(f: Fuel) -> Fuel { return f; }\n",
        &[],
    ),
    (
        "send_twice",
        "module sigil;\ncap type Fuel {}\nactor Worker { init(seed: i64) {} on Burn(f: Fuel) {} }\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(worker: ActorRef<Worker>) -> i64 { let c = fuel.split(50); worker.send(Burn(c)); worker.send(Burn(c)); return 1; }\n}\n",
        &["O001"],
    ),
    (
        "o007_borrow_then_spawn",
        "module sigil;\ncap type Fuel {}\nactor Worker { init(f: Fuel) {} on Ping() -> i64 { return 0; } }\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { let c = fuel.split(50); let bor = &c; let a = spawn::<Worker>(c); return 1; }\n}\n",
        &["O007"],
    ),
    // Sweep folds (Phase-0 O001 sweep, all matched first-try):
    // triple-move pins the O001 COUNT+ORDER (2 codes); dup-in-one-call pins the intra-statement
    // duplicate (arg-by-arg marking); restrict-twice pins restrict as a MOVE independently;
    // draw-after-move pins draw as a USE-CHECK (fires O001 after a prior move) — the mirror of
    // draw_twice (draw is not a move).
    (
        "triple_move",
        "module sigil;\ncap type Fuel {}\nfn f(x: Fuel) -> i64 { return 1; }\nfn go(c: Fuel) -> i64 { let a = f(c); let b = f(c); let d = f(c); return a; }\n",
        &["O001", "O001"],
    ),
    (
        "dup_in_one_call",
        "module sigil;\ncap type Fuel {}\nfn two(x: Fuel, y: Fuel) -> i64 { return 1; }\nfn go(c: Fuel) -> i64 { return two(c, c); }\n",
        &["O001"],
    ),
    (
        "restrict_twice",
        "module sigil;\ncap type Fuel { burn, query }\nfn go(f: Fuel) -> i64 { let a = f.restrict(burn); let b = f.restrict(query); return 1; }\n",
        &["O001"],
    ),
    (
        "draw_after_move",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(x: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a = need(f); let b = f.draw(5); return a; }\n",
        &["O001"],
    ),
    // OWN-2 O007 folds (Phase-0 sweep, all matched first-try): the fuel_cap is the LAST spawn arg,
    // so borrowed LAST and non-last args both fire O007; calls share the same consuming-site rule;
    // and O007 fires for a module-fn param cap too.
    (
        "o007_last_arg",
        "module sigil;\ncap type Fuel {}\nactor Worker { init(a: Fuel, b: Fuel) {} on Ping() -> i64 { return 0; } }\nentry actor Main {\n    state { fa: Fuel, fb: Fuel }\n    on Start() -> i64 { let x = fa.split(50); let y = fb.split(10); let bor = &y; let w = spawn::<Worker>(x, y); return 1; }\n}\n",
        &["O007"],
    ),
    (
        "o007_first_arg",
        "module sigil;\ncap type Fuel {}\nactor Worker { init(a: Fuel, b: Fuel) {} on Ping() -> i64 { return 0; } }\nentry actor Main {\n    state { fa: Fuel, fb: Fuel }\n    on Start() -> i64 { let x = fa.split(50); let y = fb.split(10); let bor = &x; let w = spawn::<Worker>(x, y); return 1; }\n}\n",
        &["O007"],
    ),
    (
        "o007_call",
        "module sigil;\ncap type Fuel {}\nfn need(x: Fuel) -> i64 { return 1; }\nfn go(c: Fuel) -> i64 { let bor = &c; let a = need(c); return a; }\n",
        &["O007"],
    ),
    (
        "o007_param_cap",
        "module sigil;\ncap type Fuel {}\nactor Worker { init(a: Fuel) {} on Ping() -> i64 { return 0; } }\nfn helper(f: Fuel) -> i64 { let bor = &f; let w = spawn::<Worker>(f); return 1; }\n",
        &["O007"],
    ),
];

/// OWN-0: the oracle's O-code list matches the pinned expectation on every corpus fixture. These
/// pins are the ground truth the OWN-1/2 shadow is diffed against; an oracle drift surfaces here.
#[test]
fn own0_oracle_pins() {
    for (label, src, expected) in OWN_CORPUS {
        let exp: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        assert_eq!(
            own_oracle_codes(label, src),
            exp,
            "SH-OWN {label}: the oracle O-code list drifted from the OWN-0 pin:\n{src}"
        );
    }
}

/// CFG move state reaches joins and loop back-edges, while a returning branch contributes no state
/// to its sibling continuation.
#[test]
fn own0_cfg_move_state_is_propagated() {
    let straight = "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a = need(f); let b = need(f); return a; }\n";
    let if_split = "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, cond: bool) -> i64 { if cond { let x = need(f); } let y = need(f); return y; }\n";
    let returning_branch = "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, cond: bool) -> i64 { if cond { let x = need(f); return x; } let y = need(f); return y; }\n";
    let loop_move = "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, cond: bool) -> i64 { while cond { let x = need(f); } return 0; }\n";
    assert_eq!(
        own_oracle_codes("blockbound_straight", straight),
        vec!["O001".to_string()],
        "straight-line double-move must fire O001"
    );
    assert_eq!(
        own_oracle_codes("blockbound_if", if_split),
        vec!["O001".to_string()],
        "a move on one predecessor must remain moved after the join"
    );
    assert_eq!(
        own_oracle_codes("returning_branch", returning_branch),
        Vec::<String>::new(),
        "a path that returns must not contaminate its sibling continuation"
    );
    assert_eq!(
        own_oracle_codes("loop_move", loop_move),
        vec!["O001".to_string()],
        "a move in a potentially repeating loop must be seen on the back-edge"
    );
}

#[test]
fn own0_cfg_borrow_state_is_propagated() {
    let branch_move = "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, cond: bool) -> i64 { let bor = &f; if cond { let x = need(f); } return 0; }\n";
    let returning_borrow = "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, cond: bool) -> i64 { if cond { let bor = &f; return 1; } let y = need(f); return y; }\n";
    assert_eq!(
        own_oracle_codes("branch_move_while_borrowed", branch_move),
        vec!["O007".to_string()],
        "an outer-scope borrow must reach a consuming successor block"
    );
    assert_eq!(
        own_oracle_codes("returning_borrow", returning_borrow),
        Vec::<String>::new(),
        "a borrow on a returning path must not contaminate its sibling continuation"
    );
}

/// Determinism: two oracle runs render identically per fixture.
#[test]
fn own0_oracle_deterministic() {
    for (label, src, _) in OWN_CORPUS {
        assert_eq!(
            own_oracle_codes(label, src),
            own_oracle_codes(label, src),
            "SH-OWN {label}: oracle must be deterministic"
        );
    }
}

#[test]
fn malformed_air_cfg_fails_closed_without_panicking() {
    let source = SourceFile::new(
        "<malformed-air>",
        "module sigil;\nfn go() -> i64 { return 0; }\n",
    );
    let (ast, parse_diagnostics) = parser::parse(&source);
    assert!(parse_diagnostics.is_empty());
    let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
    let (typed, _) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .expect("fixture must type-check");
    let valid = air::lower(&typed);
    ownership::verify(&valid).expect("control AIR must verify");

    let missing = air::BlockId(u32::MAX);
    let spare = air::BlockId(u32::MAX - 1);
    let entry = valid.functions[0].entry_block;
    let mut cases = Vec::new();

    let mut duplicate = valid.clone();
    let duplicate_block = duplicate.functions[0].blocks[0].clone();
    duplicate.functions[0].blocks.push(duplicate_block);
    cases.push(("duplicate block", duplicate));

    let mut missing_entry = valid.clone();
    missing_entry.functions[0].entry_block = missing;
    cases.push(("missing entry", missing_entry));

    let mut missing_successor = valid.clone();
    missing_successor.functions[0].blocks[0].terminator = air::AirTerminator::Jump(missing);
    cases.push(("missing reachable successor", missing_successor));

    let mut unreachable_bad_edge = valid.clone();
    let mut unreachable = unreachable_bad_edge.functions[0].blocks[0].clone();
    unreachable.id = spare;
    unreachable.terminator = air::AirTerminator::Jump(missing);
    unreachable_bad_edge.functions[0].blocks.push(unreachable);
    cases.push(("missing unreachable successor", unreachable_bad_edge));

    let mut missing_merge = valid.clone();
    missing_merge.functions[0].blocks[0].terminator = air::AirTerminator::Branch {
        cond: air::VarId(0),
        then_block: entry,
        else_block: entry,
        merge_block: Some(missing),
    };
    cases.push(("missing structural merge", missing_merge));

    let mut missing_dispatch_exit = valid.clone();
    missing_dispatch_exit.functions[0].blocks[0].terminator = air::AirTerminator::Dispatch {
        start: entry,
        exit: missing,
    };
    cases.push(("missing dispatch exit", missing_dispatch_exit));

    for (label, program) in cases {
        let result = std::panic::catch_unwind(|| ownership::verify(&program));
        let diagnostics = result
            .unwrap_or_else(|_| panic!("{label}: malformed AIR must not panic"))
            .unwrap_err();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code().to_string() == "I001"),
            "{label}: malformed AIR must return I001, got {diagnostics:?}"
        );
    }
}

// ── OWN-1: the selfhost O001 shadow lane ────────────────────────────────────────────────
//
// Composes lexer+parser+typecheck+own_check into a tool emitting a `;`-joined `O001;` stream.
// Compared EXACTLY (order-preserving, no dedup) against the oracle's {O001} list over the
// straight-line, cap-only OWN_CORPUS. (O007 is OWN-2; the OWN-1 shadow emits O001 only, so the
// o007_borrow_then_spawn fixture — whose oracle set is [O007], no O001 — is a natural accept here.)

fn own_tool(body: &str) -> String {
    let lexer_defs = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser_defs = PARSER.replace("\nmodule parser;\n", "\n");
    let tc_defs = TYPECHECK.replace("\nmodule typecheck;\n", "\n");
    let own_defs = OWNCHECK.replace("\nmodule own_check;\n", "\n");
    format!(
        "module tool;\n{lexer_defs}\n{parser_defs}\n{tc_defs}\n{own_defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn own_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = own_encode(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

fn own_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        compile_tool(&own_tool(own_body()))
            .expect("own_check tool should compile")
            .wasm
    })
}

/// The shadow's O-code list: the `;`-joined stream split (order kept, no dedup).
fn own_shadow_codes(src: &str) -> Vec<String> {
    let result = execute_ephemeral(own_wasm(), src.as_bytes(), OWN_FUEL, &IoGrants::none())
        .expect("own_check tool executes");
    let out = String::from_utf8(result.output).expect("tool output is UTF-8");
    out.split(';')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect()
}

/// OWN-1/2: the selfhost ownership verdict (O001 use-after-move + O007 move-while-borrowed) equals
/// the oracle's full {O001, O007} list, EXACTLY and in program order, over the straight-line
/// cap-only corpus.
#[test]
fn own_verdict_parity() {
    for (label, src, _) in OWN_CORPUS {
        assert_eq!(
            own_shadow_codes(src),
            own_oracle_codes(label, src),
            "SH-OWN {label}: the selfhost O-code verdict must match the oracle:\n{src}"
        );
    }
}

/// Non-stub: the shadow produces both non-empty AND empty streams across the corpus.
#[test]
fn own1_non_stub() {
    let any = OWN_CORPUS
        .iter()
        .any(|(_, src, _)| !own_shadow_codes(src).is_empty());
    let some_clean = OWN_CORPUS
        .iter()
        .any(|(_, src, _)| own_shadow_codes(src).is_empty());
    assert!(any, "SH-OWN: the shadow never fires O001 (stub)");
    assert!(
        some_clean,
        "SH-OWN: the shadow fires on every fixture (over-reports)"
    );
}

/// Determinism: two runs of the compiled shadow render identically.
#[test]
fn own1_shadow_deterministic() {
    for (_, src, _) in OWN_CORPUS {
        assert_eq!(
            own_shadow_codes(src),
            own_shadow_codes(src),
            "SH-OWN: the shadow must be deterministic:\n{src}"
        );
    }
}
