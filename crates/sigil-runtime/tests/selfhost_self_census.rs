//! SH-SELF-0 — the self-application census: every selfhost lane over the selfhost source itself.
//!
//! The self-host certification SCOPING INSTRUMENT: one
//! lane-dispatch mega-tool (all 11 selfhost modules composed, the proven boot_tool pattern) runs
//! each lane independently over each selfhost module + the COMPOSED Stage-1 source, and every
//! (module × lane) cell is PINNED to an outcome class:
//!   CLEAN        — the lane ran with no diagnostics, poison, or trap. Parity is not claimed.
//!   PARSE:{n}    — n parser error nodes (P_K_ERR kind 900; the parser is no-trap, ET-P8, so
//!                  this scan is the ONLY parse-failure observable — X-S5).
//!   REJECT{...}  — the sorted-dedup diagnostic code set (the actionable inventory).
//!   POISON       — a `!!` out-of-surface sentinel in the lane output.
//!   TRAP / FUEL  — the tool trapped (incl. alloc/OOM) or exhausted fuel (recorded outcomes).
//!
//! The pins are the RATCHET: each fixed gap flips a cell by explicit edit, so the matrix doubles
//! as the self-hosting progress tracker.
//!
//! Artifact rule (X-S9): per-module rows of modules that call ANOTHER module's helpers
//! (air.sigil → tc_*, pipeline.sigil → every lane's encode) emit unresolved-callee codes that
//! are COMPOSITION ARTIFACTS, not surface gaps — the COMPOSED row is ground truth; the doc
//! table classifies every per-module code {gap | artifact}.

/// The census fuel budget. BOOT-0 proved 300M for a SMALL program's lex+parse; whole-module
/// lanes over 311KB air.sigil are the stressor — this is the MEASURED ceiling (X-S1; raise
/// only on a measured FUEL cell, hard cap 5B).
const CENSUS_FUEL: u64 = 3_000_000_000;
/// The AIR source is the per-module stressor and now exceeds the ordinary tool's 16 MB linear-
/// memory envelope during census parsing. Keep the runtime default unchanged and raise only this
/// explicitly measured instrumentation row.
const AIR_CENSUS_BUDGET: usize = 32 * 1024 * 1024;
/// SELF-4: the per-call memory budget for the COMPOSED Stage-1 row. Measured 2026-07-14:
/// every single-gate lane completes at 64 MB, the full `all` chain at 128 MB (peak fuel
/// 74 M — 40x under CENSUS_FUEL). 256 MB = measured x2 headroom, 4x under the 1 GiB
/// runtime ceiling. Every per-module row keeps the DEFAULT 16 MB sandbox.
const SELF4_CENSUS_BUDGET: usize = 256 * 1024 * 1024;

/// The 11 selfhost modules, row order = composition order.
const SELF_MODULES: &[(&str, &str)] = &[
    ("lexer", include_str!("../../../selfhost/lexer.sigil")),
    ("parser", include_str!("../../../selfhost/parser.sigil")),
    (
        "name_resolution",
        include_str!("../../../selfhost/name_resolution.sigil"),
    ),
    (
        "typecheck",
        include_str!("../../../selfhost/typecheck.sigil"),
    ),
    (
        "ring_check",
        include_str!("../../../selfhost/ring_check.sigil"),
    ),
    (
        "effect_check",
        include_str!("../../../selfhost/effect_check.sigil"),
    ),
    (
        "taint_check",
        include_str!("../../../selfhost/taint_check.sigil"),
    ),
    (
        "cap_check",
        include_str!("../../../selfhost/cap_check.sigil"),
    ),
    (
        "own_check",
        include_str!("../../../selfhost/own_check.sigil"),
    ),
    ("air", include_str!("../../../selfhost/air.sigil")),
    ("pipeline", include_str!("../../../selfhost/pipeline.sigil")),
];

const LANES: &[&str] = &[
    "parse", "nr", "tc", "ring", "effect", "taint", "cap", "own", "all",
];

/// Strip a module's `\nmodule X;\n` header so it composes into `module tool;` (each selfhost
/// file opens with a leading comment BEFORE its module decl — the standing convention).
fn strip(src: &str, header: &str) -> String {
    src.replace(header, "\n")
}

/// The composed selfhost compiler source WITHOUT a tool body — the shared prefix of both the
/// census tool and the Stage-1 source.
fn composed_modules() -> String {
    let mut s = String::from("module tool;\n");
    for (name, src) in SELF_MODULES {
        let header = format!("\nmodule {name};\n");
        s.push_str(&strip(src, &header));
        s.push('\n');
    }
    s
}

/// The `sh_compile` tool body — VERBATIM the Stage-1 body from pipeline_differential.rs
/// (the composed row's src is exactly what Stage-1 would ingest, X-S4).
fn sh_tool_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = sh_compile(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

/// The census dispatch body: `{lane};{src}` (FIRST-`;` split, X-S6) → lex+parse once →
/// the P_K_ERR (kind 900) scan (X-S5) → the requested lane's encode, raw output.
fn census_body() -> &'static str {
    r#"    let opt: Option<str> = input_ptr.from_bytes(input_len);
    let raw: str = opt.unwrap_or("");
    let rlen: i64 = raw.len();
    let mut semi: i64 = 0 - 1;
    let mut si: i64 = 0;
    while si < rlen {
        let sb: i64 = raw.byte_at(si);
        if sb == 59 {
            semi = si;
            si = rlen;
        } else {
            si = si + 1;
        }
    }
    let lane: str = raw.substr(0, semi);
    let src: str = raw.substr(semi + 1, rlen);
    let toks: Vec<Token> = lex(src);
    let mut nodes: Arena<PNode> = Arena::new();
    let mut kids: Vec<i64> = Vec::new();
    let root: i64 = parser_parse(src, toks, nodes, kids);
    let ncount: i64 = nodes.len();
    let mut perrs: i64 = 0;
    let mut pj: i64 = 0;
    while pj < ncount {
        let pn: PNode = nodes.get(pj);
        if pn.kind == 900 {
            perrs = perrs + 1;
        } else {
        }
        pj = pj + 1;
    }
    if perrs > 0 {
        let pnum: str = ai_int_to_str(perrs);
        let ppre: str = "PARSE:";
        let pout: str = ppre.concat(pnum);
        return pout.as_output();
    } else {
    }
    let lparse: str = "parse";
    if lane.bytes_eq(lparse) {
        let pok: str = "PARSE:0";
        return pok.as_output();
    } else {
    }
    let lnr: str = "nr";
    if lane.bytes_eq(lnr) {
        let onr: str = nr_encode(nodes, kids, root);
        return onr.as_output();
    } else {
    }
    let ltc: str = "tc";
    if lane.bytes_eq(ltc) {
        let otc: str = tc_encode(nodes, kids, root);
        return otc.as_output();
    } else {
    }
    let lring: str = "ring";
    if lane.bytes_eq(lring) {
        let oring: str = rc_encode(nodes, kids, root);
        return oring.as_output();
    } else {
    }
    let leffect: str = "effect";
    if lane.bytes_eq(leffect) {
        let oeff: str = ec_encode(nodes, kids, root);
        return oeff.as_output();
    } else {
    }
    let ltaint: str = "taint";
    if lane.bytes_eq(ltaint) {
        let otaint: str = tt_encode(nodes, kids, root);
        return otaint.as_output();
    } else {
    }
    let lcap: str = "cap";
    if lane.bytes_eq(lcap) {
        let ocap: str = cap_verdict_encode(nodes, kids, root);
        return ocap.as_output();
    } else {
    }
    let lown: str = "own";
    if lane.bytes_eq(lown) {
        let oown: str = own_encode(nodes, kids, root);
        return oown.as_output();
    } else {
    }
    let lall: str = "all";
    if lane.bytes_eq(lall) {
        let oall: str = sh_compile(nodes, kids, root);
        return oall.as_output();
    } else {
    }
    let bad: str = "BADLANE";
    return bad.as_output();"#
}

fn tool_with_body(body: &str) -> String {
    format!(
        "{}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n",
        composed_modules()
    )
}

/// The Stage-1 source — the composed row's input (X-S4).
fn stage1_source() -> String {
    tool_with_body(sh_tool_body())
}

fn census_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        sigil_compiler::compile_tool(&tool_with_body(census_body()))
            .expect("the census mega-tool should compile")
            .wasm
    })
}

/// Run one census cell; returns the raw tool output or the trap/fuel class.
fn census_raw(lane: &str, src: &str) -> Result<String, String> {
    let input = format!("{lane};{src}");
    match sigil_runtime::execute_ephemeral(
        census_wasm(),
        input.as_bytes(),
        CENSUS_FUEL,
        &sigil_runtime::grants::IoGrants::none(),
    ) {
        Ok(result) => Ok(String::from_utf8_lossy(&result.output).into_owned()),
        Err(e) => {
            let msg = format!("{e:?}");
            if msg.to_lowercase().contains("fuel") {
                Err("FUEL".to_string())
            } else {
                Err("TRAP".to_string())
            }
        }
    }
}

/// SELF-4: census_raw under a raised per-call memory budget (the composed Stage-1 row
/// outgrows the 16 MB default; every other row keeps the default sandbox).
fn census_raw_budgeted(lane: &str, src: &str, budget: usize) -> Result<String, String> {
    let input = format!("{lane};{src}");
    match sigil_runtime::execute_ephemeral_with_memory_budget(
        census_wasm(),
        input.as_bytes(),
        CENSUS_FUEL,
        budget,
        &sigil_runtime::grants::IoGrants::none(),
    ) {
        Ok(result) => Ok(String::from_utf8_lossy(&result.output).into_owned()),
        Err(e) => {
            let msg = format!("{e:?}");
            if msg.to_lowercase().contains("fuel") {
                Err("FUEL".to_string())
            } else {
                Err("TRAP".to_string())
            }
        }
    }
}

fn census_cell_budgeted(lane: &str, src: &str, budget: usize) -> String {
    classify(lane, census_raw_budgeted(lane, src, budget))
}

/// The n-th `|`-segment of a lane output (nr = `records|pool|aliases|diags`, tc =
/// `records|pool|diags`).
fn pipe_seg(out: &str, n: usize) -> &str {
    out.split('|').nth(n).unwrap_or("")
}

/// Sorted-dedup code set from a `;`-joined stream (span-adopted entries `T060,81,82` reduce to
/// the code token).
fn code_set(stream: &str) -> Vec<String> {
    let mut v: Vec<String> = stream
        .split(';')
        .filter(|s| !s.is_empty())
        .map(|s| s.split(',').next().unwrap_or(s).to_string())
        .collect();
    v.sort();
    v.dedup();
    v
}

/// Classify one cell's outcome (the pin string).
fn classify(lane: &str, raw: Result<String, String>) -> String {
    let out = match raw {
        Err(class) => return class,
        Ok(o) => o,
    };
    if out.starts_with("PARSE:") {
        return out.trim().to_string();
    }
    if out.contains("!!") {
        return "POISON".to_string();
    }
    let codes = match lane {
        "nr" => code_set(pipe_seg(&out, 3)),
        "tc" => code_set(pipe_seg(&out, 2)),
        "ring" | "effect" | "taint" | "cap" | "own" => code_set(&out),
        "all" => {
            if out.starts_with("OK:") {
                return "CLEAN".to_string();
            }
            let rest = out.strip_prefix("REJECT:").unwrap_or(&out);
            let (stage, codes) = rest.split_once(':').unwrap_or(("?", rest));
            return format!("REJECT:{stage}{{{}}}", code_set(codes).join(","));
        }
        _ => return format!("UNKNOWN-LANE:{out}"),
    };
    if codes.is_empty() {
        "CLEAN".to_string()
    } else {
        format!("REJECT{{{}}}", codes.join(","))
    }
}

fn census_cell(lane: &str, src: &str) -> String {
    classify(lane, census_raw(lane, src))
}

// ── The canaries (must pass before any selfhost pin is trusted) ─────────────────────────────

/// X-S7: the dispatch canary — known programs through every lane must reproduce the outputs
/// the existing differentials pin (kills a mis-mapped lane token AND proves the first-`;`
/// split: every src below is semicolon-dense).
#[test]
fn census_dispatch_canary() {
    let scalar = "module m;\nfn f(a: i64, b: i64) -> i64 { return a + b; }\n";
    assert_eq!(census_cell("parse", scalar), "PARSE:0", "parse lane");
    assert_eq!(census_cell("nr", scalar), "CLEAN", "nr lane clean");
    assert_eq!(census_cell("tc", scalar), "CLEAN", "tc lane clean");
    assert_eq!(census_cell("all", scalar), "CLEAN", "all lane accept");

    let tc_bad = "module m; fn f() -> i64 { let x: bool = 5; return 0; }";
    assert_eq!(
        census_cell("tc", tc_bad),
        "REJECT{T041}",
        "tc lane maps to tc_encode"
    );

    let nr_bad = "module a;\nuse missing;\nfn f() -> i64 { return 0; }\nmodule b;\nfn g() -> i64 { return 1; }\n";
    assert_eq!(
        census_cell("nr", nr_bad),
        "REJECT{N007}",
        "nr lane maps to nr_encode"
    );

    let ring_bad =
        "#[ring(outer)] module m;\ncap type Fuel { burn }\nfn f(c: Fuel) -> i64 { return 0; }\n";
    assert_eq!(
        census_cell("ring", ring_bad),
        "REJECT{R001}",
        "ring lane maps to rc_encode"
    );

    let effect_bad = "#[ring(outer)]\nmodule m;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} { return expensive(); }\n";
    assert_eq!(
        census_cell("effect", effect_bad),
        "REJECT{E001}",
        "effect lane maps to ec_encode"
    );

    let taint_bad = "module ext;\nfn leak() -> i64 @Secret {\n    let s: i64 @Secret = 0;\n    return s;\n}\nfn f() -> i64 {\n    let y: i64 @Public = leak();\n    return 0;\n}\n";
    assert_eq!(
        census_cell("taint", taint_bad),
        "REJECT{T001}",
        "taint lane maps to tt_encode"
    );

    let cap_bad = "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return need(r); }\n";
    assert_eq!(
        census_cell("cap", cap_bad),
        "REJECT{C003}",
        "cap lane maps to cap_verdict_encode"
    );

    let own_bad = "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a = need(f); let b = need(f); return a; }\n";
    assert_eq!(
        census_cell("own", own_bad),
        "REJECT{O001}",
        "own lane maps to own_encode"
    );
}

/// X-S8: the rig canary — the smallest module through the cheapest lanes MUST run; if even
/// this can't, the rig itself is broken and no pin is trustworthy.
#[test]
fn census_rig_canary() {
    let pipeline_src = SELF_MODULES
        .iter()
        .find(|(n, _)| *n == "pipeline")
        .unwrap()
        .1;
    assert_eq!(
        census_cell("parse", pipeline_src),
        "PARSE:0",
        "pipeline.sigil must parse"
    );
    let nr = census_cell("nr", pipeline_src);
    assert!(
        nr == "CLEAN" || nr.starts_with("REJECT"),
        "pipeline.sigil × nr must RUN (got {nr})"
    );
}

// ── The pinned census matrix (measured 2026-07-08; the RATCHET — a fix flips a cell by
//    explicit edit only, X-S3). Lane order: parse, nr, tc, ring, effect, taint, cap, own, all.
//
//    THE MEASURED PICTURE: every module PARSES clean under its declared census budget. Isolated
//    cross-module type/callee references explain the remaining tc codes; they vanish in composition.
//    Known unsupported taint shapes now reject explicitly instead of being classified CLEAN.
//    SELF-1 FINDING (2026-07-12): the per-module T046 is a MIX — (a) the stdlib-generic-let gap
//    (`let v: Vec<i64>` — a REAL tc-shadow gap the oracle accepts via ambient injection; REMOVED by
//    SELF-1's tc_stdlib_generic_arity, pinned CLEAN in self1_stdlib_generic_let_accepted) PLUS (b) a
//    cross-module-plain-type artifact (`let cn: PNode` — PNode is defined in another selfhost
//    module, unknown to the ISOLATED tc, so T046 fires at the unknown-plain-name site; like T062 it
//    is a COMPOSITION ARTIFACT that vanishes at BOOT-SELF and is CORRECT isolated behavior — the
//    oracle rejects the isolated module too). So these per-module rows RETAIN T046 (the artifact
//    (b) remains); SELF-1's win is composition-invariant, not a per-module pin flip. The former
//    AIR and COMPOSED traps were census-memory envelopes; their explicit 32/256 MB budgets keep
//    the ordinary 16 MB runtime default unchanged. ─────────────────────────────────────────

/// The self-contained modules that RETAIN {T046, T060} after SELF-1+SELF-2 (parser/name_resolution/
/// typecheck). Both are now the SAME cross-module composition ARTIFACT, NOT a real gap: these
/// modules reference another module's TYPES/CONSTS (Token/PNode; parser's P_K_* consts), unknown to
/// the isolated tc → T046 (a cross-module TYPE annotation) + T060 (a cross-module CONST reference or
/// a field access on a cross-module-typed local). Correct isolated behavior (the oracle rejects the
/// isolated module too), vanishing at BOOT-SELF. SELF-2 removed their SAME-module T060 (consts +
/// tuples + record-annotation authority) but the cross-module residue remains. lexer → ROW_LEXER
/// (the base module, no cross-module refs → fully tc-clean). The `all` lane no longer stops at
/// tc: gate 2 filters the artifact codes (the sibling-gate discipline; see pipeline.sigil), so
/// the isolated module falls through to the standalone emitter surface and POISONS,
/// fail-closed-loud.
const ROW_SELF_CONTAINED: [&str; 9] = [
    "PARSE:0",
    "CLEAN",
    "REJECT{T046,T060}",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "REJECT:tc{T060}",
];

/// Parser's taint lane became CLEAN with the all-public tuple-let/break arms (HB-2 rung 1) —
/// its unsupported shapes were exactly those two. Its isolated tc LANE still reports the
/// cross-module artifacts raw, but the `all` lane's gate 2 now FILTERS the artifact codes
/// (T046/T060/T062/T071 — the sibling-gate discipline; see pipeline.sigil), so the isolated
/// module falls through the whole chain to emission — where the 224 KB standalone parse tree
/// TRAPS the default 16 MB census sandbox. Fail-closed (a trap, loud), and the per-module
/// budget deliberately stays the default (only AIR and COMPOSED carry measured raises).
const ROW_PARSER: [&str; 9] = [
    "PARSE:0",
    "CLEAN",
    "REJECT{T046,T060}",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "REJECT:tc{T060}",
];

/// The cross-calling modules that RETAIN {T046, T060, T062} after SELF-1+SELF-2 (ring/effect/taint/
/// cap/own): ALL THREE are X-S9 composition artifacts — T046 (a cross-module type annotation), T060
/// (a cross-module const reference / field access on a cross-module-typed local), T062 (a
/// cross-module callee). Correct isolated behavior; all vanish at BOOT-SELF. SELF-2 removed their
/// same-module T060; the cross-module residue remains. pipeline → ROW_PIPELINE (threads via calls,
/// so it carries only the T062 callee artifact — its T060 was purely same-module consts, now gone).
/// The `all` lane: gate 2 filters the artifact codes, so these rows fall through to the
/// standalone emitter surface and POISON, fail-closed-loud (same story as ROW_LEXER).
const ROW_CROSS_CALLER: [&str; 9] = [
    "PARSE:0",
    "CLEAN",
    "REJECT{T046,T060,T062}",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "REJECT:tc{T060,T062}",
];

/// lexer — the base module, references NO other module's types/consts — is now FULLY tc-CLEAN.
/// SELF-1 removed its stdlib-generic T046; SELF-2 removed its remaining T060 (same-module consts +
/// tuple destructure + plain-record-annotation authority for `let t: Token = toks.get(i)`). The
/// taint lane became CLEAN when the shadow gained all-public tuple-let/break arms (HB-2 rung 1):
/// lexer's only unsupported shapes were exactly those. That un-masks the `all` lane's
/// downstream emitter surface again — this census row emits WITHOUT mn_expand or the stdlib
/// (`sh_tool_body`), and on that standalone surface the W-lane poisons, fail-closed-loud
/// (the state this row pinned before the taint boundary short-circuited it; the certified
/// cap0 surface — with monomorph + stdlib — emits poison-FREE, `cap0_poison_census_ratchet`).
const ROW_LEXER: [&str; 9] = [
    "PARSE:0", "CLEAN", "CLEAN", "CLEAN", "CLEAN", "CLEAN", "CLEAN", "CLEAN", "POISON",
];

/// pipeline — its T060 (same-module consts) is gone after SELF-2; T062 (the X-S9 cross-module
/// callee artifact) remains. It threads nodes/kids through CALLS, not re-annotated cross-module
/// locals, so it carries no T046/cross-module-type T060 artifact.
const ROW_PIPELINE: [&str; 9] = [
    "PARSE:0",
    "CLEAN",
    "REJECT{T062}",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "CLEAN",
    "REJECT:tc{T062}",
];

fn assert_row(name: &str, src: &str, want: &[&str; 9]) {
    let mut drift = Vec::new();
    for (lane, expected) in LANES.iter().zip(want.iter()) {
        let got = if name == "air" {
            census_cell_budgeted(lane, src, AIR_CENSUS_BUDGET)
        } else {
            census_cell(lane, src)
        };
        if &got != expected {
            drift.push(format!("{name} × {lane}: actual {got}, pinned {expected}"));
        }
    }
    assert!(
        drift.is_empty(),
        "SH-SELF census drift (the ratchet moves by explicit edit only):\n{}",
        drift.join("\n")
    );
}

fn module_src(name: &str) -> &'static str {
    SELF_MODULES.iter().find(|(n, _)| *n == name).unwrap().1
}

/// SELF-1: the stdlib-generic let-annotation false positive is gone. A `let v: Vec<i64>` (and
/// Arena/Map) is now CLEAN through the selfhost tc — mirroring the trusted oracle, which accepts
/// these via ambient stdlib injection (`record Vec<T>` → `resolve_annotated_let_type` accepts at
/// matching arity). The ALLOWLIST boundary (not a blanket accept): an UNKNOWN generic base or a
/// WRONG-arity known generic still REJECTs with T046, exactly as the oracle does.
/// SELF-1: the stdlib-generic let-annotation false positive is gone. A `let v: Vec<i64>`
/// (Arena/Map, scalar OR record arg, `mut` or not) is now CLEAN through the selfhost tc —
/// mirroring the trusted oracle, which accepts these via ambient stdlib injection
/// (`record Vec<T>` → `resolve_annotated_let_type` accepts at matching arity). The ALLOWLIST
/// boundary (not a blanket accept): an UNKNOWN generic base or a WRONG-arity known generic still
/// REJECTs with T046, exactly as the oracle does.
///
/// This is the SELF-1 ratchet (each `CLEAN` below was `REJECT{T046}` before the fix). It is NOT a
/// per-module census pin flip: the per-module rows RETAIN T046 from a SEPARATE, correct source —
/// a cross-module plain-type annotation (`let n: PNode`, PNode defined in another module) fires
/// T046 at the unknown-plain-name site in the ISOLATED tc. That is a composition artifact (like
/// T062), not a gap — it vanishes at BOOT-SELF (one module, PNode defined) and the oracle rejects
/// the isolated module too. `xmod_artifact` pins that it is retained.
#[test]
fn self1_stdlib_generic_let_accepted() {
    // positive — an allowlisted stdlib generic at correct arity is CLEAN (scalar/record arg, mut).
    let vec_let = "module m; fn f() -> i64 { let v: Vec<i64> = Vec::new(); return 0; }";
    assert_eq!(census_cell("tc", vec_let), "CLEAN", "Vec<i64> let accepted");
    let vec_mut = "module m; fn f() -> i64 { let mut v: Vec<str> = Vec::new(); return 0; }";
    assert_eq!(
        census_cell("tc", vec_mut),
        "CLEAN",
        "let mut Vec<str> accepted"
    );
    let arena_let = "module m; fn f() -> i64 { let a: Arena<i64> = Arena::new(); return 0; }";
    assert_eq!(
        census_cell("tc", arena_let),
        "CLEAN",
        "Arena<i64> let accepted"
    );
    let map_let = "module m; fn f() -> i64 { let mp: Map<i64, i64> = Map::new(); return 0; }";
    assert_eq!(
        census_cell("tc", map_let),
        "CLEAN",
        "Map<i64,i64> let accepted"
    );

    // composition-invariant — a SINGLE module (the BOOT-SELF shape: every type defined locally)
    // that uses a local record AND a stdlib-generic let is fully CLEAN (no T046 at all).
    let composed = "module m; record R { x: i64 } fn f() -> i64 { let r: R = R { x: 1 }; let v: Vec<R> = Vec::new(); return 0; }";
    assert_eq!(
        census_cell("tc", composed),
        "CLEAN",
        "local record + Vec<R> let, no T046"
    );

    // negative (E1) — an UNKNOWN generic base still fires T046 (the allowlist is not a blanket).
    let unknown = "module m; fn f() -> i64 { let x: Bogus<i64> = 0; return 0; }";
    assert_eq!(
        census_cell("tc", unknown),
        "REJECT{T046}",
        "unknown generic base still T046"
    );

    // negative (E1b) — a KNOWN stdlib generic at the WRONG arity still fires T046 (oracle parity).
    let wrong_arity = "module m; fn f() -> i64 { let mp: Map<i64> = 0; return 0; }";
    assert_eq!(
        census_cell("tc", wrong_arity),
        "REJECT{T046}",
        "wrong-arity Map still T046"
    );

    // the composition ARTIFACT, retained: a cross-module plain-type let (PNode undefined here)
    // fires T046 at the unknown-plain-name site — correct isolated behavior, vanishes at BOOT-SELF.
    let xmod_artifact = "module m; fn f() -> i64 { let n: PNode = 0; return 0; }";
    assert_eq!(
        census_cell("tc", xmod_artifact),
        "REJECT{T046}",
        "cross-module plain type still T046"
    );
}

/// SELF-2: the T060 "undefined local" gap. The SELF-0 census labeled T060 "tuples", but a
/// bisection showed it is DOMINATED by a different same-module gap — MODULE CONSTANTS (the tc shadow
/// had no P_K_CONST handling, so every T_*/P_K_*/TC_* reference — 228 in lexer alone — false-fired
/// T060). SELF-2 closes the full SAME-module T060 gap: (1) module consts (tc_seed_consts), (2) tuple
/// destructure (the P_K_LET_TUPLE binding arm), (3) plain-record-annotation authority
/// (`let t: Token = toks.get(i)` binds t as Token so `t.kind` resolves). Each CLEAN below was
/// REJECT{T060} before. Boundary: a genuinely-undefined name and a CROSS-MODULE const (defined in
/// another module, unknown to the isolated tc — a composition artifact like T062) still fire T060.
#[test]
fn self2_tc_t060_gap_closed() {
    // (2) tuple destructure — the element names bind.
    let tup = "module m; fn pair() -> (i64, i64) { return (1, 2); } fn f() -> i64 { let (a, b) = pair(); return a + b; }";
    assert_eq!(
        census_cell("tc", tup),
        "CLEAN",
        "let-tuple destructure binds"
    );
    // (1) module const reference in a comparison.
    let konst = "module m; const T_EOF: i64 = 0; fn f(k: i64) -> i64 { if k == T_EOF { return 1; } else { return 0; } }";
    assert_eq!(census_cell("tc", konst), "CLEAN", "module const ref binds");
    // (3) plain-record annotation authority — field access on an out-of-core-VALUED record local.
    let fld = "module m; record Token { kind: i64 } fn f(toks: Vec<Token>) -> i64 { let t: Token = toks.get(0); return t.kind; }";
    assert_eq!(
        census_cell("tc", fld),
        "CLEAN",
        "record-annotated local resolves fields"
    );

    // boundary — a genuinely-undefined local still fires T060 (no over-suppression).
    let undef = "module m; fn f() -> i64 { return zzz; }";
    assert_eq!(
        census_cell("tc", undef),
        "REJECT{T060}",
        "genuine undefined still T060"
    );
    // boundary — a CROSS-MODULE const (P_K_FN is defined in parser) is unknown to the isolated tc,
    // so it stays T060: a composition artifact (correct isolated behavior, vanishes at BOOT-SELF).
    let xmod =
        "module m; fn f(cn: i64) -> i64 { if cn == P_K_FN { return 1; } else { return 0; } }";
    assert_eq!(
        census_cell("tc", xmod),
        "REJECT{T060}",
        "cross-module const still T060 (artifact)"
    );
}

#[test]
fn census_row_lexer() {
    // SELF-2: lexer is now FULLY tc-CLEAN (SELF-1 T046 + SELF-2 T060: consts + tuple destructure +
    // plain-record-annotation authority; the base module carries no cross-module artifact). The
    // `all` POISON is a newly-exposed downstream (air/wasm) limit, not a tc issue. See ROW_LEXER.
    assert_row("lexer", module_src("lexer"), &ROW_LEXER);
}
#[test]
fn census_row_parser() {
    assert_row("parser", module_src("parser"), &ROW_PARSER);
}
#[test]
fn census_row_name_resolution() {
    assert_row(
        "name_resolution",
        module_src("name_resolution"),
        &ROW_SELF_CONTAINED,
    );
}
#[test]
fn census_row_typecheck() {
    assert_row("typecheck", module_src("typecheck"), &ROW_SELF_CONTAINED);
}
#[test]
fn census_row_ring_check() {
    assert_row("ring_check", module_src("ring_check"), &ROW_CROSS_CALLER);
}
#[test]
fn census_row_effect_check() {
    assert_row(
        "effect_check",
        module_src("effect_check"),
        &ROW_CROSS_CALLER,
    );
}
#[test]
fn census_row_taint_check() {
    assert_row("taint_check", module_src("taint_check"), &ROW_CROSS_CALLER);
}
#[test]
fn census_row_cap_check() {
    assert_row("cap_check", module_src("cap_check"), &ROW_CROSS_CALLER);
}
#[test]
fn census_row_own_check() {
    assert_row("own_check", module_src("own_check"), &ROW_CROSS_CALLER);
}
#[test]
fn census_row_pipeline() {
    // SELF-2: pipeline's T060 (same-module consts) is gone; T062 (the cross-module callee
    // composition artifact) remains. See ROW_PIPELINE.
    assert_row("pipeline", module_src("pipeline"), &ROW_PIPELINE);
}
/// AIR is the per-module memory stressor. Under its explicit 32 MB census budget it parses and
/// fails soft with the expected isolated cross-module type/callee diagnostics.
#[test]
fn census_row_air() {
    assert_row(
        "air",
        module_src("air"),
        &[
            "PARSE:0",
            "CLEAN",
            "REJECT{T046,T060,T062}",
            "CLEAN",
            "CLEAN",
            "CLEAN",
            "CLEAN",
            "CLEAN",
            "REJECT:tc{T060,T062}",
        ],
    );
}
/// Under the measured 256 MB per-call budget, the COMPOSED Stage-1 source parses cleanly and
/// EVERY gate lane — nr/tc/ring/effect/taint/cap/own — is clean: with the all-public
/// tuple-let/break arms (HB-2 rung 1), the composed compiler's own source passes its own full
/// gate chain. The `all` lane now reaches emission and POISONS, fail-closed-loud: THIS row's
/// tool is `sh_tool_body` — no mn_expand, no stdlib — and that standalone emitter surface is
/// outside the W-lane (the taint short-circuit was masking it). The certified surface with
/// monomorph + stdlib emits poison-free (`cap0_poison_census_ratchet`) and, gates included,
/// byte-identically (the HB-2 rung-0 census measured OK: + the exact certified module size).
#[test]
fn census_row_composed() {
    let composed = stage1_source();
    let mut drift = Vec::new();
    for (lane, expected) in LANES.iter().zip(
        [
            "PARSE:0", "CLEAN", "CLEAN", "CLEAN", "CLEAN", "CLEAN", "CLEAN", "CLEAN", "POISON",
        ]
        .iter(),
    ) {
        let got = census_cell_budgeted(lane, &composed, SELF4_CENSUS_BUDGET);
        if &got != expected {
            drift.push(format!(
                "COMPOSED × {lane}: actual {got}, pinned {expected}"
            ));
        }
    }
    assert!(
        drift.is_empty(),
        "SH-SELF census drift (the ratchet moves by explicit edit only):\n{}",
        drift.join("\n")
    );
}

/// X-BMEM: the DEFAULT 16 MB sandbox is unchanged — the composed row still TRAPs without the
/// explicit per-call budget (the raise is per-execution, never ambient).
#[test]
fn census_row_composed_default_sandbox_fence() {
    let composed = stage1_source();
    assert_eq!(
        census_cell("parse", &composed),
        "TRAP",
        "the default sandbox must still bound the composed row"
    );
}

/// Sampled determinism (one mid-size row × all lanes, twice — not 108×2 re-runs).
#[test]
fn census_deterministic_sample() {
    let src = module_src("taint_check");
    for lane in LANES {
        assert_eq!(
            census_cell(lane, src),
            census_cell(lane, src),
            "census must be deterministic: taint_check × {lane}"
        );
    }
}
