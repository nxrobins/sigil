//! SH-BOOT — the composed self-hosted compiler differential (`sh_compile`).
//!
//! The bootstrap's achievable core: ONE composed tool that IS the self-hosted compiler — source in,
//! the checker gates in the oracle's stage order, byte-identical WASM out — on the covered
//! certified subset. The current guarantees and boundaries are documented in
//! docs/specs/self-hosting-completion-ladder.md.
//!
//! THE ORACLE IS THE STAGE CHAIN, NOT `compile_tool` (X-B1): this harness builds sigil-compiler
//! `default-features = false` (no solver), so `compile_tool`'s capability::verify would run
//! armor-only and silently ACCEPT cap-violating fixtures. `oracle_compile` mirrors the exact
//! solver-free gates the shipped lanes verified: name_resolution → type_check → ring_check →
//! effect_check → taint_check → air::lower → bitwise-C003-from-the-Pure-collector-workload
//! (== Z3 on slot-free, the CAP-0 solver-lane proof) → ownership::verify → the W-lane byte target
//! `wasm::emit(&fuel::insert(memory::lower(air)).0).inner`. Each stage short-circuits — the
//! first failing stage's codes win (X-B2, mirroring compiler.rs:951-977's `?` chain).
//!
//! The protocol (frozen, X-B3): `REJECT:{stage}:{codes}` (stage ∈ {nr, tc, ring, effect, taint,
//! cap, own}; codes = that lane's CORE-filtered `;`-joined stream) or `OK:{hex}` (the W-lane
//! lowercase-hex whole-module transport). Comparison is STRUCTURED per stage — each lane's shipped
//! convention (sorted-dedup SETS for nr/tc/ring/effect/taint, ordered lists for cap/own, the FULL
//! hex string for accepts) — never weaker than the lane that shipped it.

use sigil_compiler::CompileOptions;
use sigil_compiler::air;
use sigil_compiler::air_capability_v2;
use sigil_compiler::effect_check;
use sigil_compiler::fuel;
use sigil_compiler::memory;
use sigil_compiler::name_resolution;
use sigil_compiler::ownership;
use sigil_compiler::parser;
use sigil_compiler::ring_check;
use sigil_compiler::source::SourceFile;
use sigil_compiler::taint_check;
use sigil_compiler::type_check;
use sigil_compiler::wasm;

/// The per-lane CORE code surfaces (each lane's shipped filter, reused exactly — MI-4).
const CORE_R_CODES: &[&str] = &["R001", "R003"];
const CORE_E_CODES: &[&str] = &["E001", "E002"];
const CORE_TAINT_CODES: &[&str] = &[
    "T001", "T020", "T021", "T022", "T023", "T024", "T025", "T026", "T027", "T029", "T030", "T031",
    "T032",
];

/// Render a diagnostic list to the lane's `;`-joined stream (order-preserving; the comparison layer
/// applies the per-lane set/list convention).
fn codes_stream(codes: &[String]) -> String {
    let mut s = String::new();
    for c in codes {
        s.push_str(c);
        s.push(';');
    }
    s
}

/// The oracle compiler: the solver-free stage chain with first-fail gating, emitting the frozen
/// protocol. Panics (naming the fixture) only on a PARSE failure — parse-clean is the ambient
/// corpus contract; everything downstream is in-protocol.
fn oracle_compile(label: &str, src: &str) -> String {
    let source = SourceFile::new("<boot-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(
        pdiags.is_empty(),
        "SH-BOOT {label}: fixture must be parse-clean, got {:?}\n{src}",
        pdiags
            .iter()
            .map(|d| d.code().to_string())
            .collect::<Vec<_>>()
    );

    // Gate 1: name resolution (N-codes).
    let resolved = match name_resolution::resolve(&ast) {
        Ok(r) => r,
        Err(ds) => {
            let codes: Vec<String> = ds.iter().map(|d| d.code().to_string()).collect();
            return format!("REJECT:nr:{}", codes_stream(&codes));
        }
    };

    // Gate 2: type check (T-codes; also yields the AuthorityRegistry for the cap gate).
    let (typed, registry) =
        match type_check::check_with_options(&resolved, &CompileOptions::default()) {
            Ok(pair) => pair,
            Err(ds) => {
                let codes: Vec<String> = ds.iter().map(|d| d.code().to_string()).collect();
                return format!("REJECT:tc:{}", codes_stream(&codes));
            }
        };

    // Gate 3: ring check (CORE = {R001, R003}).
    if let Err(ds) = ring_check::check_rings(&typed) {
        let codes: Vec<String> = ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| CORE_R_CODES.contains(&c.as_str()))
            .collect();
        if !codes.is_empty() {
            return format!("REJECT:ring:{}", codes_stream(&codes));
        }
    }

    // Gate 4: effect check (CORE = {E001, E002}).
    if let Err(ds) = effect_check::check_effects(&typed) {
        let codes: Vec<String> = ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| CORE_E_CODES.contains(&c.as_str()))
            .collect();
        if !codes.is_empty() {
            return format!("REJECT:effect:{}", codes_stream(&codes));
        }
    }

    // Gate 5: taint check (the 13 in-core scalar codes).
    if let Err(ds) = taint_check::check_taints(&typed) {
        let codes: Vec<String> = ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| CORE_TAINT_CODES.contains(&c.as_str()))
            .collect();
        if !codes.is_empty() {
            return format!("REJECT:taint:{}", codes_stream(&codes));
        }
    }

    // AIR lowering (infallible), then the AIR-level gates.
    let lowered = air::lower(&typed);

    // Gate 6: capability — the bitwise C003 verdict from the Z3-free Pure collector workload
    // (== the Z3 discharge on slot-free programs; the CAP-0 solver-lane equivalence proof).
    let (_, workload) =
        air_capability_v2::collect_air_capability_workload_for_test(&lowered, &registry);
    let cap_codes: Vec<String> = workload
        .obligations
        .iter()
        .filter(|o| o.actual_mask & o.required_mask != o.required_mask)
        .map(|_| "C003".to_string())
        .collect();
    if !cap_codes.is_empty() {
        return format!("REJECT:cap:{}", codes_stream(&cap_codes));
    }

    // Gate 7: ownership (CORE = {O001, O007}, ordered).
    if let Err(ds) = ownership::verify(&lowered) {
        let codes: Vec<String> = ds
            .iter()
            .map(|d| d.code().to_string())
            .filter(|c| c == "O001" || c == "O007")
            .collect();
        if !codes.is_empty() {
            return format!("REJECT:own:{}", codes_stream(&codes));
        }
    }

    // All gates clean: the W-lane byte target.
    let (mem_p, _) = memory::lower(lowered);
    let (fuel_p, _) = fuel::insert(mem_p);
    let out = wasm::emit(&fuel_p);
    assert!(
        out.outer.is_none(),
        "SH-BOOT {label}: X-W7 — unexpected outer-ring module:\n{src}"
    );
    let hex: String = out.inner.iter().map(|b| format!("{b:02x}")).collect();
    format!("OK:{hex}")
}

/// Split a protocol string into (kind, stage, payload). `OK` has stage "".
fn split_protocol(out: &str) -> (String, String, String) {
    if let Some(hex) = out.strip_prefix("OK:") {
        return ("OK".to_string(), String::new(), hex.to_string());
    }
    let rest = out.strip_prefix("REJECT:").expect("protocol prefix");
    let (stage, codes) = rest.split_once(':').expect("protocol stage separator");
    ("REJECT".to_string(), stage.to_string(), codes.to_string())
}

/// Normalize a stage's code stream per its lane's shipped comparison convention: sorted-dedup SETS
/// for nr/tc/ring/effect/taint (count parity was each lane's explicit AG), ordered lists for
/// cap/own (their shadows were verified ordered).
fn normalize_codes(stage: &str, codes: &str) -> Vec<String> {
    let mut v: Vec<String> = codes
        .split(';')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect();
    match stage {
        "cap" | "own" => v,
        _ => {
            v.sort();
            v.dedup();
            v
        }
    }
}

/// Compare two protocol outputs with the per-lane conventions. Returns a mismatch description.
fn protocol_eq(a: &str, b: &str) -> Result<(), String> {
    let (ka, sa, pa) = split_protocol(a);
    let (kb, sb, pb) = split_protocol(b);
    if ka != kb {
        return Err(format!("kind {ka} != {kb}"));
    }
    if sa != sb {
        return Err(format!("stage {sa} != {sb}"));
    }
    if ka == "OK" {
        if pa != pb {
            return Err("wasm hex differs".to_string());
        }
        return Ok(());
    }
    let na = normalize_codes(&sa, &pa);
    let nb = normalize_codes(&sb, &pb);
    if na != nb {
        return Err(format!("codes {na:?} != {nb:?}"));
    }
    Ok(())
}

// ── BOOT-0 Phase-0: the first-fail gate-order pins ──────────────────────────────────────
//
// The oracle short-circuits at the first failing stage; a fixture violating TWO stages must
// report only the EARLIER stage's codes. These pins are the gate-order ground truth the BOOT-1
// selfhost driver must reproduce.

#[test]
fn boot0_first_fail_order() {
    // ring + cap violations: ring gates first (an outer-ring cap param [R001] whose cap is also
    // attenuated at a call [would-be C003]).
    let ring_and_cap = "#[ring(outer)] module m;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return need(r); }\n";
    let out = oracle_compile("ring_and_cap", ring_and_cap);
    let (kind, stage, _) = split_protocol(&out);
    assert_eq!(
        (kind.as_str(), stage.as_str()),
        ("REJECT", "ring"),
        "ring must gate before cap: {out}"
    );

    // cap + own violations: cap gates first (an attenuated cap at a call [C003] that is also
    // consumed twice [would-be O001]).
    let cap_and_own = "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); let a = need(r); let b = need(r); return a; }\n";
    let out2 = oracle_compile("cap_and_own", cap_and_own);
    let (kind2, stage2, _) = split_protocol(&out2);
    assert_eq!(
        (kind2.as_str(), stage2.as_str()),
        ("REJECT", "cap"),
        "cap must gate before own: {out2}"
    );

    // own-only: a full-authority double-consume reaches the own gate.
    let own_only = "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a = need(f); let b = need(f); return a; }\n";
    let out3 = oracle_compile("own_only", own_only);
    let (kind3, stage3, codes3) = split_protocol(&out3);
    assert_eq!(
        (kind3.as_str(), stage3.as_str()),
        ("REJECT", "own"),
        "a clean-cap double-consume must reach the own gate: {out3}"
    );
    assert_eq!(normalize_codes("own", &codes3), vec!["O001".to_string()]);

    // an accept: the canonical covered program emits OK + non-empty hex.
    let accept = "module m;\nfn f(a: i64, b: i64) -> i64 { return a + b; }\n";
    let out4 = oracle_compile("accept_scalar", accept);
    let (kind4, _, hex4) = split_protocol(&out4);
    assert_eq!(
        kind4, "OK",
        "the covered scalar program must compile: {out4}"
    );
    assert!(!hex4.is_empty() && hex4.len() % 2 == 0, "well-formed hex");
}

/// Determinism: the oracle driver is stable per fixture.
#[test]
fn boot0_oracle_deterministic() {
    let fixtures = [
        "module m;\nfn f(a: i64, b: i64) -> i64 { return a + b; }\n",
        "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a = need(f); let b = need(f); return a; }\n",
    ];
    for src in fixtures {
        assert_eq!(
            oracle_compile("det", src),
            oracle_compile("det", src),
            "oracle_compile must be deterministic"
        );
    }
}

/// The protocol comparison layer itself (unit sanity — a wrong-stage or wrong-code mismatch is
/// caught and described).
#[test]
fn boot0_protocol_comparison() {
    assert!(protocol_eq("OK:00asm", "OK:00asm").is_ok());
    assert!(protocol_eq("OK:00", "OK:01").is_err());
    assert!(protocol_eq("REJECT:ring:R001;R001;", "REJECT:ring:R001;").is_ok()); // set-lane dedup
    assert!(protocol_eq("REJECT:own:O001;O001;", "REJECT:own:O001;").is_err()); // ordered lane
    assert!(protocol_eq("REJECT:ring:R001;", "REJECT:cap:C003;").is_err()); // stage mismatch
}

// ── BOOT-0: the mega-composition feasibility smoke (X-B4, bounds from MEASUREMENT) ─────
//
// Phase-0 measured (2026-07-08): the full composition (all 10 selfhost modules, 21,712 lines /
// ~910KB source) compiles via compile_tool in 0.5s to a 381KB wasm module, and a lex+parse run
// executes in 0.07s under FUEL=300M. The bounds below are those measurements rounded UP to loud
// ceilings (CI variance headroom) — a regression past them is a real composition problem.

/// Strip every selfhost module header and concatenate ALL stages into one `module tool;` around
/// `body` — the SH-BOOT mega-tool composition (prefix-disjoint helpers; textually collision-free).
fn boot_tool(body: &str) -> String {
    let strip = |src: &str, header: &str| src.replace(header, "\n");
    let lexer = strip(
        include_str!("../../../selfhost/lexer.sigil"),
        "\nmodule lexer;\n",
    );
    let parser_s = strip(
        include_str!("../../../selfhost/parser.sigil"),
        "\nmodule parser;\n",
    );
    let nr = strip(
        include_str!("../../../selfhost/name_resolution.sigil"),
        "\nmodule name_resolution;\n",
    );
    let tc = strip(
        include_str!("../../../selfhost/typecheck.sigil"),
        "\nmodule typecheck;\n",
    );
    let rc = strip(
        include_str!("../../../selfhost/ring_check.sigil"),
        "\nmodule ring_check;\n",
    );
    let ec = strip(
        include_str!("../../../selfhost/effect_check.sigil"),
        "\nmodule effect_check;\n",
    );
    let tt = strip(
        include_str!("../../../selfhost/taint_check.sigil"),
        "\nmodule taint_check;\n",
    );
    let cap = strip(
        include_str!("../../../selfhost/cap_check.sigil"),
        "\nmodule cap_check;\n",
    );
    let own = strip(
        include_str!("../../../selfhost/own_check.sigil"),
        "\nmodule own_check;\n",
    );
    let air_s = strip(
        include_str!("../../../selfhost/air.sigil"),
        "\nmodule air;\n",
    );
    let pipe = strip(
        include_str!("../../../selfhost/pipeline.sigil"),
        "\nmodule pipeline;\n",
    );
    format!(
        "module tool;\n{lexer}\n{parser_s}\n{nr}\n{tc}\n{rc}\n{ec}\n{tt}\n{cap}\n{own}\n{air_s}\n{pipe}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// The measured ceilings (X-B4): compile <= 30s, module <= 4 MB, and a lex+parse run completes
/// under the standard 300M fuel.
#[test]
fn boot0_mega_composition_feasible() {
    use std::time::Instant;
    let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);
         let src: str = opt.unwrap_or(\"\");
         let toks: Vec<Token> = lex(src);
         let mut nodes: Arena<PNode> = Arena::new();
         let mut kids: Vec<i64> = Vec::new();
         let root: i64 = parser_parse(src, toks, nodes, kids);
         let rn: PNode = nodes.get(root);
         let enc: str = cap_i64_str(rn.kind);
         return enc.as_output();";
    let tool = boot_tool(body);
    let t0 = Instant::now();
    let res = sigil_compiler::compile_tool(&tool)
        .expect("the SH-BOOT mega-composition must compile (all 10 modules, prefix-disjoint)");
    let dt = t0.elapsed();
    assert!(
        dt.as_secs() <= 30,
        "X-B4: composed-tool compile took {:.1}s (> the measured 0.5s x60 ceiling)",
        dt.as_secs_f64()
    );
    assert!(
        res.wasm.len() <= 4 * 1024 * 1024,
        "X-B4: composed module {} bytes (> the measured 381KB ~10x ceiling)",
        res.wasm.len()
    );
    let run = sigil_runtime::execute_ephemeral(
        &res.wasm,
        b"module m;
fn f(a: i64) -> i64 { return a + 1; }
",
        300_000_000,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("a lex+parse through the mega-tool must run under 300M fuel");
    assert_eq!(
        String::from_utf8_lossy(&run.output),
        "1",
        "the parse root must be a P_K_MODULE (kind 1)"
    );
}

// ── BOOT-1: the composed self-hosted compiler lane ──

/// The sh_compile tool body: lex → parse → the full gate chain → the protocol string.
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

fn sh_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        sigil_compiler::compile_tool(&boot_tool(sh_tool_body()))
            .expect("the sh_compile mega-tool should compile")
            .wasm
    })
}

/// Run the self-hosted compiler on `src`, returning its protocol string.
fn sh_compile_out(src: &str) -> String {
    let result = sigil_runtime::execute_ephemeral(
        sh_wasm(),
        src.as_bytes(),
        300_000_000,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the sh_compile tool executes");
    String::from_utf8(result.output).expect("tool output is UTF-8")
}

/// The BOOT corpus: (label, fixture, the intended stage — "OK" for accepts). The intended
/// stage double-pins the oracle (the corpus cannot silently drift to a different gate).
const BOOT_CORPUS: &[(&str, &str, &str)] = &[
    // Accepts — the covered monomorphic surface, byte-identical WASM.
    (
        "a_scalar",
        "module m;\nfn f(a: i64, b: i64) -> i64 { return a + b; }\n",
        "OK",
    ),
    (
        "a_cf_while",
        "module m;\nfn f(n: i64) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < n { s = s + i; i = i + 1; } return s; }\n",
        "OK",
    ),
    (
        "a_record_method",
        "module m;\nrecord P { x: i64 }\nimpl P { pub fn get(self: P) -> i64 { return self.x; } }\nfn f(p: P) -> i64 { return p.get(); }\n",
        "OK",
    ),
    (
        "a_record_construct",
        "module m;\nrecord P { x: i64, y: i64 }\nfn f(a: i64, b: i64) -> i64 { let p: P = P { x: a, y: b }; return p.x + p.y; }\n",
        "OK",
    ),
    (
        "a_if_else",
        "module m;\nfn f(a: i64, b: i64) -> i64 { if a < b { return b; } else { return a; } }\n",
        "OK",
    ),
    (
        "a_call_chain",
        "module m;\nfn helper(x: i64) -> i64 { return x + 1; }\nfn f(a: i64) -> i64 { let r: i64 = helper(a); return r; }\n",
        "OK",
    ),
    // a_effrow_resolved GUARDS the tc bare-name-registration fix (typecheck.sigil:3603/3691):
    // an effect-row fn (`! { Alloc }`) whose call must RESOLVE through the tc census — without
    // the fix it false-fires T062 (undefined callee) and this accept goes RED.
    (
        "a_effrow_resolved",
        "module m;\nfn a() -> i64 ! { Alloc } { return 7; }\nfn b() -> i64 { let r: i64 = a(); return r; }\n",
        "OK",
    ),
    // Rejects — one per gate, each within its lane's covered reject surface.
    (
        "r_nr_unresolved_use",
        "module a;\nuse missing;\nfn f() -> i64 { return 0; }\nmodule b;\nfn g() -> i64 { return 1; }\n",
        "nr",
    ),
    (
        "r_tc_let_mismatch",
        "module m; fn f() -> i64 { let x: bool = 5; return 0; }",
        "tc",
    ),
    (
        "r_ring_cap_param",
        "#[ring(outer)] module m;\ncap type Fuel { burn }\nfn f(c: Fuel) -> i64 { return 0; }\n",
        "ring",
    ),
    (
        "r_effect_call_leak",
        "#[ring(outer)]\nmodule m;\neffect NetIO;\nfn expensive() -> i64 ! { NetIO } { return 0; }\nfn boot() -> i64 ! {} { return expensive(); }\n",
        "effect",
    ),
    (
        "r_taint_leak",
        "module ext;\nfn leak() -> i64 @Secret {\n    let s: i64 @Secret = 0;\n    return s;\n}\nfn f() -> i64 {\n    let y: i64 @Public = leak();\n    return 0;\n}\n",
        "taint",
    ),
    (
        "r_cap_attenuation",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return need(r); }\n",
        "cap",
    ),
    (
        "r_own_double_consume",
        "module sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a = need(f); let b = need(f); return a; }\n",
        "own",
    ),
    // The multi-violation first-fail pins (X-B2).
    (
        "m_ring_before_cap",
        "#[ring(outer)] module m;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return need(r); }\n",
        "ring",
    ),
    (
        "m_cap_before_own",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); let a = need(r); let b = need(r); return a; }\n",
        "cap",
    ),
    (
        "m_nr_before_tc",
        "module x;\nuse missing;\nfn f() -> i64 { let b: bool = 5; return 0; }\nmodule y;\nfn g() -> i64 { return 1; }\n",
        "nr",
    ),
];

/// BOOT-1: the self-hosted compiler's protocol output equals the oracle's, structurally, over
/// the whole corpus — accepts byte-identical (full hex), rejects at the same stage with the
/// same codes (per-lane conventions). ALSO double-pins the oracle's stage against the intent.
#[test]
fn boot1_pipeline_parity() {
    for (label, src, intended) in BOOT_CORPUS {
        let oracle = oracle_compile(label, src);
        let (okind, ostage, _) = split_protocol(&oracle);
        if *intended == "OK" {
            assert_eq!(
                okind, "OK",
                "SH-BOOT {label}: intended an accept:\n{oracle}"
            );
        } else {
            assert_eq!(
                (okind.as_str(), ostage.as_str()),
                ("REJECT", *intended),
                "SH-BOOT {label}: the oracle must reject at the intended stage"
            );
        }
        let shadow = sh_compile_out(src);
        if let Err(why) = protocol_eq(&shadow, &oracle) {
            panic!(
                "SH-BOOT {label}: the self-hosted compiler diverged ({why})\nshadow: {}\noracle: {}\n{src}",
                &shadow[..shadow.len().min(120)],
                &oracle[..oracle.len().min(120)]
            );
        }
    }
}

#[test]
fn boot1_unsupported_taint_shape_fails_closed() {
    // A public `break` became a SUPPORTED shape (HB-2 rung 1), so the fixture moved to the
    // closure-capture model — still outside the shadow's projection, still fail-closed.
    let src = "module m; fn f(x: i64) -> i64 { let g = fn() -> i64 { return x; }; return 0; }";
    let oracle = oracle_compile("unsupported-taint", src);
    assert_eq!(
        split_protocol(&oracle).0,
        "OK",
        "the control must be valid production SIGIL"
    );

    let shadow = sh_compile_out(src);
    let (kind, stage, detail) = split_protocol(&shadow);
    assert_eq!((kind.as_str(), stage.as_str()), ("REJECT", "taint"));
    assert!(
        detail.contains("SH_TAINT_UNSUPPORTED"),
        "self-host rejection must name the unsupported boundary: {shadow}"
    );
}

/// The execution capstone: a covered program compiled BY THE SELF-HOSTED COMPILER runs and
/// produces the same value as the oracle-compiled module — Stage-1 compiles, and it RUNS.
#[test]
fn boot1_execution_capstone() {
    let src = "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < 10 { s = s + i; i = i + 1; } return 0 - s; }\n";
    let shadow = sh_compile_out(src);
    let (kind, _, hex) = split_protocol(&shadow);
    assert_eq!(kind, "OK", "the capstone program must compile: {shadow}");
    assert!(hex.len() % 2 == 0, "well-formed hex");
    let bytes: Vec<u8> = (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("strict hex (X-W4)"))
        .collect();
    // Byte-identity against the oracle, then RUN the self-host-compiled module. The program sums
    // 0..9 (= 45) in a while-loop and returns `0 - s` = -45; the ephemeral runtime traps a
    // negative tool return and reports its MAGNITUDE (ephemeral.rs:346 formats `-packed`), so the
    // witness is "tool returned error (45)" — proof the self-host-compiled loop ran end-to-end.
    let oracle = oracle_compile("capstone", src);
    let (_, _, ohex) = split_protocol(&oracle);
    assert_eq!(hex, ohex, "capstone: byte-identical modules");
    let run = sigil_runtime::execute_ephemeral(
        &bytes,
        b"",
        300_000_000,
        &sigil_runtime::grants::IoGrants::none(),
    );
    match run {
        Err(sigil_runtime::ToolError::Trapped { message }) => {
            assert!(
                message.contains("tool returned error (45)"),
                "the self-host-compiled loop must return -45 (reported as magnitude 45): {message}"
            );
        }
        other => panic!("expected the negative-sentinel return, got {other:?}"),
    }
}

/// Non-stub: every gate fires at least once across the corpus (MC-1 — no dead gates), and the
/// compiler accepts the covered fixtures.
#[test]
fn boot1_every_gate_fires() {
    let mut stages = std::collections::BTreeSet::new();
    let mut oks = 0usize;
    for (_, src, _) in BOOT_CORPUS {
        let (kind, stage, _) = split_protocol(&sh_compile_out(src));
        if kind == "OK" {
            oks += 1;
        } else {
            stages.insert(stage);
        }
    }
    assert!(oks >= 3, "the compiler must accept the covered fixtures");
    for want in ["nr", "tc", "ring", "effect", "taint", "cap", "own"] {
        assert!(
            stages.contains(want),
            "the {want} gate never fired (a dead gate — MC-1); fired: {stages:?}"
        );
    }
}

/// Determinism: two runs of the composed compiler produce identical protocol strings.
#[test]
fn boot1_deterministic() {
    for (_, src, _) in BOOT_CORPUS {
        assert_eq!(
            sh_compile_out(src),
            sh_compile_out(src),
            "sh_compile must be deterministic:\n{src}"
        );
    }
}

// ── MONO-4 Phase-0: sh_compile + mn_expand on generic programs ────────────────────────────────

/// The BOOT mega-tool + monomorph.sigil composed; body = parse -> mn_expand -> sh_compile.
fn boot_mono_tool(body: &str) -> String {
    let base = boot_tool(body);
    // splice the monomorph module in right before the pipeline module (both prefix-disjoint;
    // mn_expand uses only tc_ helpers, all already present).
    let mn =
        include_str!("../../../selfhost/monomorph.sigil").replace("\nmodule monomorph;\n", "\n");
    // insert after the air module — boot_tool emits "{air_s}\n{pipe}"; splice mn between them by
    // appending before the tool_main (the modules all precede the body).
    let marker = "\npub fn tool_main(";
    let idx = base.find(marker).expect("tool_main present");
    format!("{}\n{}\n{}", &base[..idx], mn, &base[idx..])
}

fn sh_mono_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let e: i64 = mn_expand(nodes, kids, root);\n\
     \x20   let enc: str = sh_compile(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

// ── MONO-4: sh_compile + mn_expand — the composed self-hosted compiler accepts generics ──────

fn sh_mono_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        sigil_compiler::compile_tool(&boot_mono_tool(sh_mono_body()))
            .expect("the mono-sh mega-tool (all 11 modules + monomorph) should compile")
            .wasm
    })
}

fn sh_mono_out(src: &str) -> String {
    let result = sigil_runtime::execute_ephemeral(
        sh_mono_wasm(),
        src.as_bytes(),
        300_000_000,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the mono-sh tool executes");
    String::from_utf8(result.output).expect("tool output is UTF-8")
}

/// MONO-4 corpus: whole `module tool;` programs. Generic accepts (bare-T free fns) that the
/// composed compiler monomorphizes; plus a non-generic accept (mn_expand is a no-op) and a
/// non-generic reject (the gate chain still fires, unaffected by the mn_expand pass).
const MONO4_CORPUS: &[(&str, &str, &str)] = &[
    (
        "g_id",
        "module tool;\nfn id<T>(x: T) -> T { return x; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = id(25); let b: i64 = id(16); return 0 - (a + b); }\n",
        "OK",
    ),
    (
        "g_pair",
        "module tool;\nfn pair<A, B>(a: A, b: B) -> A { return a; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let r: i64 = pair(41, true); return 0 - r; }\n",
        "OK",
    ),
    (
        "g_two_types",
        "module tool;\nfn id<T>(x: T) -> T { return x; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = id(25); let f: bool = id(true); return 0 - a; }\n",
        "OK",
    ),
    (
        "g_cf",
        "module tool;\nfn id<T>(x: T) -> T { return x; }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < 3 { let d: i64 = id(i); s = s + d; i = i + 1; } return 0 - s; }\n",
        "OK",
    ),
    // Folded sweep permanents (4/4, 2026-07-12): a record-typed instance, and the nested
    // generic call (id(id(41))) through the FULL gate chain (the deferred-patch guard).
    (
        "g_record_targ",
        "module tool;
record P { x: i64 }
fn idr<T>(x: T) -> i64 { return 7; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let p: P = P { x: 1 }; let r: i64 = idr(p); return 0 - r; }
",
        "OK",
    ),
    (
        "g_nested",
        "module tool;
fn id<T>(x: T) -> T { return x; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = id(id(41)); return 0 - a; }
",
        "OK",
    ),
    // mn_expand is a no-op on a monomorphic program — the composed output is unchanged.
    (
        "m_scalar",
        "module m;\nfn f(a: i64, b: i64) -> i64 { return a + b; }\n",
        "OK",
    ),
    // the gate chain still REJECTS after the (no-op) mn_expand pass — a tc mismatch.
    (
        "r_tc",
        "module m; fn f() -> i64 { let x: bool = 5; return 0; }",
        "tc",
    ),
    // MONO-8: the MONO-5/6/7 expansion classes through the FULL gate chain (nr→tc→ring→effect→
    // taint→cap→own→wasm), not just the W-lane. Transitive was already clean; records + methods
    // needed the tc-gate T046 relaxation (a base-named construct conforms to a `base__…` instance
    // annotation). Each ACCEPTs byte-identically to the oracle's whole-pipeline verdict.
    (
        "g8_transitive",
        "module tool;\nfn f3<T>(x: T) -> T { return x; }\nfn f2<T>(x: T) -> T { return f3(x); }\nfn f1<T>(x: T) -> T { return f2(x); }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: i64 = f1(41); return 0 - a; }\n",
        "OK",
    ),
    (
        "g8_record",
        "module tool;\nrecord Box<T> { v: T }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; return 0 - b.v; }\n",
        "OK",
    ),
    (
        "g8_record_mixed",
        "module tool;\nrecord P<T> { a: T, b: bool }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let p: P<i64> = P { a: 41, b: true }; return 0 - p.a; }\n",
        "OK",
    ),
    (
        "g8_method",
        "module tool;\nrecord Box<T> { v: T }\nimpl Box<T> { pub fn get(self: Box<T>) -> T { return self.v; } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 41 }; return 0 - b.get(); }\n",
        "OK",
    ),
    (
        "g8_method_arg",
        "module tool;\nrecord Box<T> { v: T }\nimpl Box<T> { pub fn add(self: Box<T>, k: i64) -> i64 { return self.v + k; } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let b: Box<i64> = Box { v: 40 }; return 0 - b.add(1); }\n",
        "OK",
    ),
    (
        "g8_method_two_inst",
        "module tool;\nrecord Box<T> { v: T }\nimpl Box<T> { pub fn id(self: Box<T>) -> T { return self.v; } }\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let a: Box<i64> = Box { v: 41 }; let c: Box<bool> = Box { v: true }; let d: bool = c.id(); return 0 - a.id(); }\n",
        "OK",
    ),
];

/// MONO-4: `sh_compile(mn_expand(src))` == the oracle's whole pipeline verdict over the corpus —
/// generic ACCEPTS byte-identical (the composed self-hosted compiler monomorphizes), plus the
/// no-op + reject controls.
#[test]
fn mono4_composed_parity() {
    for (label, src, intended) in MONO4_CORPUS {
        let oracle = oracle_compile(label, src);
        let (okind, ostage, _) = split_protocol(&oracle);
        if *intended == "OK" {
            assert_eq!(okind, "OK", "MONO-4 {label}: intended an accept:\n{oracle}");
        } else {
            assert_eq!(
                (okind.as_str(), ostage.as_str()),
                ("REJECT", *intended),
                "MONO-4 {label}: the oracle must reject at the intended stage"
            );
        }
        let shadow = sh_mono_out(src);
        if let Err(why) = protocol_eq(&shadow, &oracle) {
            panic!(
                "MONO-4 {label}: the composed mono-compiler diverged ({why})\nshadow: {}\noracle: {}\n{src}",
                &shadow[..shadow.len().min(120)],
                &oracle[..oracle.len().min(120)]
            );
        }
    }
}

/// The execution capstone: a GENERIC program compiled by the composed self-hosted compiler
/// (sh_compile + mn_expand) RUNS to the same value as the oracle-compiled program.
#[test]
fn mono4_execution_capstone() {
    let src = MONO4_CORPUS[0].1; // g_id: 0 - (id(25) + id(16)) = -41
    let shadow = sh_mono_out(src);
    let (kind, _, hex) = split_protocol(&shadow);
    assert_eq!(
        kind, "OK",
        "the composed compiler must accept the generic capstone: {shadow}"
    );
    let bytes: Vec<u8> = (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("strict hex"))
        .collect();
    let oracle = oracle_compile("cap", src);
    let (_, _, ohex) = split_protocol(&oracle);
    assert_eq!(hex, ohex, "capstone: byte-identical whole module");
    match sigil_runtime::execute_ephemeral(
        &bytes,
        b"",
        300_000_000,
        &sigil_runtime::grants::IoGrants::none(),
    ) {
        Err(sigil_runtime::ToolError::Trapped { message }) => assert!(
            message.contains("tool returned error (41)"),
            "the self-host-monomorphized generic program must return -41: {message}"
        ),
        other => panic!("expected the neg-sentinel trap, got {other:?}"),
    }
}

/// Determinism.
#[test]
fn mono4_deterministic() {
    for (_, src, _) in MONO4_CORPUS {
        assert_eq!(
            sh_mono_out(src),
            sh_mono_out(src),
            "the composed mono-compiler must be deterministic"
        );
    }
}

// ── B-COMPOSE: the B-VEC/B-LET/B-DISPATCH/B-ASSOC classes through the FULL composed gate ─────
//
// The composed self-hosted compiler (mn_expand + sh_compile: nr→tc→ring→effect→taint→cap→own→
// wasm) accepts the stdlib Vec/Arena idiom byte-identically. Two tc-gate additions made it
// pass: (1) the three vec-backing intrinsic SIGNATURES (alloc → i64; vec_load/vec_store typed
// UNHANDLED — the oracle knows them globally: user-code `alloc` ACCEPTS, `vec_load` rejects on
// a witness-shape check that stays an explicit divergence fence, quarantined out of tree);
// (2) the T049 return-path twin of MONO-8's T046 relaxation (`-> Vec__i64` — mn's annotation
// rewrite — accepts `return Vec {...}`, the instance's generic origin). Map<K,V> is DORMANT
// (zero non-comment selfhost uses — the sweep the epic plan anticipated is not needed).
fn bcompose_corpus() -> Vec<(&'static str, String)> {
    let vecsrc = include_str!("../../../stdlib/sigil/vec.sigil").replace("\nmodule vec;\n", "\n");
    let arenasrc =
        include_str!("../../../stdlib/sigil/arena.sigil").replace("\nmodule arena;\n", "\n");
    vec![
        (
            "bc_vec",
            format!(
                "module tool;\n{vecsrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut v: Vec<i64> = Vec::new(); let q: i64 = v.push(41); let x: i64 = v.get(0); return 0 - x; }}\n"
            ),
        ),
        (
            "bc_arena",
            format!(
                "module tool;\n{vecsrc}\n{arenasrc}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 !{{ Alloc }} {{ let mut a: Arena<i64> = Arena::new(); let id: i64 = a.allocate(41); let x: i64 = a.get(id); return 0 - x; }}\n"
            ),
        ),
    ]
}

/// Whole-pipeline parity: the composed compiler's verdict (OK hex) is byte-identical to the
/// oracle's on the stdlib-idiom fixtures.
#[test]
fn bcompose_composed_parity() {
    for (label, src) in &bcompose_corpus() {
        let oracle = oracle_compile(label, src);
        let (okind, _, _) = split_protocol(&oracle);
        assert_eq!(
            okind, "OK",
            "B-COMPOSE {label}: intended an accept:\n{oracle}"
        );
        let shadow = sh_mono_out(src);
        if let Err(why) = protocol_eq(&shadow, &oracle) {
            panic!(
                "B-COMPOSE {label}: the composed compiler diverged ({why})\nshadow: {}\noracle: {}",
                &shadow[..shadow.len().min(120)],
                &oracle[..oracle.len().min(120)]
            );
        }
    }
}

/// The execution capstone: the Arena lifecycle compiled BY the composed self-hosted compiler
/// (source → all gates → wasm) RUNS to -41.
#[test]
fn bcompose_execution_capstone() {
    let corpus = bcompose_corpus();
    let (_, src) = &corpus[1]; // bc_arena
    let shadow = sh_mono_out(src);
    let (kind, _, hex) = split_protocol(&shadow);
    assert_eq!(
        kind, "OK",
        "B-COMPOSE capstone: the composed compiler accepts"
    );
    let bytes: Vec<u8> = (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("hex"))
        .collect();
    match sigil_runtime::execute_ephemeral(
        &bytes,
        b"",
        300_000_000,
        &sigil_runtime::grants::IoGrants::none(),
    ) {
        Err(sigil_runtime::ToolError::Trapped { message }) => assert!(
            message.contains("tool returned error (41)"),
            "B-COMPOSE capstone: the Arena lifecycle must run to -41: {message}"
        ),
        other => panic!("expected the neg-sentinel trap, got {other:?}"),
    }
}

/// Determinism.
#[test]
fn bcompose_deterministic() {
    for (_, src) in &bcompose_corpus() {
        assert_eq!(sh_mono_out(src), sh_mono_out(src), "deterministic");
    }
}

// ── CAP-0: the BOOT-SELF capstone input + the per-fn W-emit poison census (the ratchet) ──────
//
// The capstone INPUT is the COMPILER SOURCE: the mono mega-tool minus its tool_main driver
// (the driver's `Option<str>` ingestion line is harness glue, not compiler source — excluding
// it keeps generic ENUMS out of the certified surface), with vec/arena spliced in-module and
// string/strings/option appended as modules (the oracle's str-method desugar targets
// `string::str_concat` etc. — module-qualified). The ORACLE ACCEPTS this input (Stage-2
// exists). Stage-1's W-emit poison census (`ai_wasm_poison_census`, the stage-4 instrument)
// names every fn whose emission taints — the DECREASING ratchet each W-surface slice shrinks
// (move the pin by explicit edit only). Measured classes (2026-07-14): str intrinsics
// (.len x457 mixed, .substr x109, .byte_at x55), the 5 stdlib-desugar methods (.concat x309,
// .bytes_eq x212, .join x52, .itoa x29, .contains x6), Vec/Arena (.get/.push/.set/.allocate
// x2610) already covered by the B slices; the Option/iterator tail lives ONLY in vec.sigil's
// dormant iterator section (0 compiler uses).
// W-REACH: the capstone input trims the 6 stdlib-leaf fns the
// composed compiler provably never calls (the nine `.contains("::")` edges — parser_stmt +
// 8 air.sigil sites — were rewritten to byte-scan / tc_last_colons equivalents). Line-anchored (fn-start line
// through the column-0 `}` line): brace-COUNTING is a trap — the first `{` after a
// signature can be the `! { Alloc }` effect row. A bad strip cannot be silent: the census
// tool compiles the trimmed input through the ORACLE, so a dangling caller = a loud T062.
fn cap0_strip_fn(src: &str, name: &str) -> String {
    let pat = format!("pub fn {name}(");
    let start = src.find(&pat).expect("cap0 trim: fn present");
    let line_start = src[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let end_pat = "\n}\n";
    let end = src[start..].find(end_pat).expect("cap0 trim: fn end") + start + end_pat.len();
    format!("{}{}", &src[..line_start], &src[end..])
}

// ── THE STRIP LIST ────────────────────────────────────────────────────────────────────────────
// Functions excluded from the certified input. Adding one shrinks both sides of
// the relational capstone, so fixed array sizes and `pin_strip_list_length` guard it.
const CAP0_STRIP_STRING: [&str; 1] = ["str_utoa_u64"];
const CAP0_STRIP_STRINGS: [&str; 5] = [
    "str_contains",
    "__sigil_slice_str_contains",
    "str_parse_u64",
    "str_parse_u32",
    "str_parse_i32",
];

fn cap0_input() -> String {
    let vecsrc = include_str!("../../../stdlib/sigil/vec.sigil").replace(
        "
module vec;
",
        "
",
    );
    let arenasrc = include_str!("../../../stdlib/sigil/arena.sigil").replace(
        "
module arena;
",
        "
",
    );
    let stringsrc = CAP0_STRIP_STRING.iter().fold(
        include_str!("../../../stdlib/sigil/string.sigil").to_string(),
        |s, n| cap0_strip_fn(&s, n),
    );
    let stringssrc = CAP0_STRIP_STRINGS.iter().fold(
        include_str!("../../../stdlib/sigil/strings.sigil").to_string(),
        |s, n| cap0_strip_fn(&s, n),
    );
    let optionsrc = include_str!("../../../stdlib/sigil/option.sigil");
    let base = boot_mono_tool(sh_mono_body());
    let cut = base
        .find(
            "
pub fn tool_main(",
        )
        .expect("driver present");
    let header = "module tool;
";
    let hidx = base.find(header).expect("module header") + header.len();
    format!(
        "{}{}
{}
{}
{}
{}
{}",
        &base[..hidx],
        vecsrc,
        arenasrc,
        &base[hidx..cut],
        stringsrc,
        stringssrc,
        optionsrc
    )
}

/// CAP-0 pin 1: Stage-2 EXISTS — the oracle accepts the capstone input whole-pipeline.
#[test]
fn cap0_oracle_accepts_capstone_input() {
    let input = cap0_input();
    let oracle = oracle_compile("cap0", &input);
    let (okind, _, _) = split_protocol(&oracle);
    assert_eq!(okind, "OK", "the oracle must accept the capstone input");
}

/// CAP-0 pin 2: the W-emit poison-census ratchet. Each W-surface slice SHRINKS this by
/// explicit edit; 0 = the byte capstone is unblocked. History: 422 (CAP-0 baseline) ->
/// 404 (W-STR-A) -> 387 (W-STR-B) -> 339 (W-CONST) -> 338 (W-TUPLE: tuple construct +
/// call-RHS destructure; scan_number un-poisoned. The remaining survivors' poison is
/// TRANSITIVE — parser fns call the lexer's scan_string/scan_fstring/lex_step, which need
/// the string-module desugar bodies present, and the CENSUS harness (parser+lexer+vec, no
/// string module) can't resolve str_concat, so they poison in the SUBSET census but not in
/// the full CAP-0 composed input. The true W-TAIL remainder is f-strings + escape-concat
/// shapes, measured against the full input next) -> 339 (W-ELEM: +1 EXPLICIT — the new
/// cv_vec_elem_tok helper joins the census. The W-ELEM payoff is invisible to this counter:
/// it fixed the SILENT class (record/str Vec elements emitted same-length-but-WRONG i64 ops,
/// poison-free, so never counted here). The dump also showed the
/// 339 split cleanly: every fn touching a Vec/Arena/env method poisons IN THIS COMPOSED
/// CONTEXT while the identical shapes are byte-identical in small fixtures (census-on-F = []),
/// and every census-absent fn is a pure scalar/str-param helper — the sharp hypothesis for the
/// context-poison diagnosis slice is mn_expand pre-resolution failing at composed scale)
/// -> 105 (W-MOD: THE ROOT CAUSE of the context poison — mn_expand had NO module descent, so
/// a multi-module input's P_K_PROGRAM root made every item scan find nothing and the whole
/// pass silently NO-OPPED (zero instances, zero pre-resolved flags -> every generic-receiver
/// method call poisoned). mn_collect_modules + per-module drives un-poisoned 234 fns at once.
/// The 105 residue is legible: Vec__get/push__bool instance fns (the W-ELEM narrow fence
/// firing LOUD on a real Vec<bool> use), field-receiver str methods (cv_env_*/tc_* — the
/// W-STR-FIELD class, now load-bearing), f-string fns (parser_fstring/lex_step/encode), and
/// method calls under statement kinds mn_expand_block does not walk (match/for bodies))
/// -> 61 (W-STR-FIELD: str methods on a one-hop field receiver — the cv_env_*/tc_* class —
/// plus the latent bare return-position arg-order fix; the 61 residue = Vec__bool instances,
/// the string-module builders, DIRECT field-receiver Vec methods (cv_field_*/tc_find_field —
/// the concrete-base-generic-field mn gap), the tc_emit_*/match cluster, and f-strings)
/// -> 56 (W-STRRAW: str_from_raw — the stdlib-private str-header intrinsic every string builder
/// calls — was undispatched in cv_emit_vecintr; adding it un-poisoned str_concat/str_join/
/// str_from_bytes/str_itoa. The str_parse_*/str_utoa/str_contains remainder poisons on a
/// DIFFERENT shape (__sigil_slice_str_contains / Vec<bool>); the residue is now field-vec
/// (AG-G19 concrete-base-generic-field) + str-slice + tc/parser transitive + Vec<bool>)
/// -> 41 (W-FIELDVEC: AG-G19 CLOSED — Vec methods on a CONCRETE record's generic field
/// (`rec.fnames.get(i)`) now resolve: mn_field_targs gates its base-targs bail on a GENERIC
/// base (a concrete base's field-type leaves are already concrete), grec holds ALL record
/// defs (B-ASSOC keeps generic-only semantics via an explicit guard), and — the empirically
/// found hidden blocker — mn_rewrite_rec_annots SKIPS record defs entirely: rewriting a
/// SOURCE record's field annotation to the instance name (`fnames: Vec__str`) forward-
/// references the appended clone def, so tc_build_recs' backward-declared-only resolution
/// left the ftag TC_UNHANDLED -> cv_recv_rec -1 -> poison; unrewritten `Vec<str>` resolves
/// to the backward-declared generic Vec, and discovery rides fn-side annotations. (A
/// prepend-the-clones variant fixed wfv but broke the generic-base bdisp/bassoc/welem
/// corpora — the skip is the placement-neutral mechanism.) The 41 residue: the lexer/parser
/// f-string+binop cluster (lex_step/encode/parser_*), str-slice, Vec<bool>)
/// -> 16 (W-INTOCONST: `op = T_PLUS;` — a top-level const as an ASSIGN RHS — was the whole
/// "clean-shaped" cluster's cause: W-CONST covered cv_to_var but cv_into (the given-dst path
/// every assign takes) lacked the const fallback; a 5-line mirror un-poisoned 25 fns (all 5
/// binop parsers + the tc_emit/tt/mn walkers + lex_step + str_contains). The 16 residue:
/// field-receiver .itoa (parser_const/emit/encode/tc_tmangle_kind/tc_emit_expr),
/// parser_type/pattern (call-in-construct-field, Vec-len-in-record-field), the Option/match
/// str_parse_* family + __sigil_slice_str_contains, and Vec<bool>)
/// -> 10 (W-FIELDITOA: itoa on a one-hop I64 field receiver — `tv.value.itoa()` — closed the
/// AG-WSF3 deferral; encode/parser_const/parser_emit/parser_type/tc_tmangle_kind/tc_emit_expr
/// un-poisoned. THE 10 RESIDUE: parser_pattern + parser_extern (construct-field shapes), the
/// Option/match str_parse_*/str_utoa_u64/str_contains/__sigil_slice_str_contains family
/// (generic-enum + narrow classes), and Vec__get/push__bool (the W-ELEM narrow fence on a
/// real use))
/// -> 8 (W-TUPELEM: the $str provenance sentinel on call-RHS tuple-destructured elements —
/// `let (btext, bend, bp) = …; btext.len()` — un-poisoned parser_pattern + parser_extern, the
/// LAST two compiler fns. THE 8 RESIDUE is stdlib-leaf + Vec<bool> ONLY: the Option/match
/// str_parse_i32/u32/u64 + str_utoa_u64 + str_contains + __sigil_slice_str_contains family,
/// and Vec__get/push__bool)
/// -> 6 (W-VECBOOL: bool joined cv_vec_elem_tok's closed set — probe-pinned i32-class ops,
/// the wa layer needed nothing; the narrow fence repointed to Vec<i32>. THE 6 RESIDUE IS
/// PURE STDLIB LEAF: str_parse_i32/u32/u64 (Option/match generic-enum + width casts),
/// str_utoa_u64 (%-mod/u64 ops), str_contains (Option-let), __sigil_slice_str_contains
/// (slice receivers) — grind-vs-accept-as-fenced is the capstone decision)
/// -> 0 (W-REACH: the reachability measurement — the 6 form a CLOSED cluster whose NINE live
/// edges were all one idiom, `.contains("::")`: parser_stmt (now an inline byte scan;
/// parser.sigil compiles standalone so no tc helpers) + 8 air.sigil sites (now
/// `tc_last_colons(text) >= 0`, air's established `::` lens). The capstone input trims the 6
/// then-dead defs from the string/strings splice (cap0_strip_fn). The FIRST trim run
/// returned 7 NEW poisoned fns — air's str_contains callers, missed because the initial grep
/// covered the 4 mono modules, not boot_tool's full include list; the census named them
/// (no tc stage in the census tool -> a dangling desugar call = fn-level poison, LOUD).
/// THE WALL IS DOWN — every fn in the capstone input emits poison-free; the remaining
/// BOOT-SELF step is the byte capstone itself: Stage-1 hex == Stage-2 + RUNS).

#[test]
fn cap0_poison_census_ratchet() {
    let input = cap0_input();
    let census_tool = {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);
         let src: str = opt.unwrap_or(\"\");
         let toks: Vec<Token> = lex(src);
         let mut nodes: Arena<PNode> = Arena::new();
         let mut kids: Vec<i64> = Vec::new();
         let root: i64 = parser_parse(src, toks, nodes, kids);
         let e: i64 = mn_expand(nodes, kids, root);
         let census: str = ai_wasm_poison_census(nodes, kids, root);
         return census.as_output();";
        boot_mono_tool(body)
    };
    let census_wasm = sigil_compiler::compile_tool(&census_tool)
        .expect("the census tool compiles")
        .wasm;
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        &census_wasm,
        input.as_bytes(),
        3_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the census executes under the SELF-4 budget");
    let out = String::from_utf8_lossy(&result.output).into_owned();
    let names: Vec<&str> = out.split(';').filter(|s| !s.is_empty()).collect();
    eprintln!("CAP-0 poison census: {} fns", names.len());
    assert_eq!(
        names.len(),
        0,
        "the poison-census ratchet moves by explicit edit only (first 10: {:?})",
        &names[..names.len().min(10)]
    );
}

/// BOOT-SELF: THE BYTE CAPSTONE — Stage-1 (the selfhost
/// compiler as WASM: lex -> parse -> mn_expand -> ai_encode_wasm over cap0_input) emits a
/// whole-module hex IDENTICAL to Stage-2 (the trusted Rust oracle, direct pipeline). The
/// This test proves byte identity only. Separate per-class capstones execute Stage-1-emitted
/// modules; the driver-less module here is not itself an executable round-trip.
#[test]
fn boot_self_byte_capstone() {
    let input = cap0_input();
    let oracle = oracle_compile("boot_self", &input);
    let (okind, _, ohex) = split_protocol(&oracle);
    assert_eq!(okind, "OK", "Stage-2 exists");
    let stage1_tool = {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);
         let src: str = opt.unwrap_or(\"\");
         let toks: Vec<Token> = lex(src);
         let mut nodes: Arena<PNode> = Arena::new();
         let mut kids: Vec<i64> = Vec::new();
         let root: i64 = parser_parse(src, toks, nodes, kids);
         let e: i64 = mn_expand(nodes, kids, root);
         let hex: str = ai_encode_wasm(nodes, kids, root);
         return hex.as_output();";
        boot_mono_tool(body)
    };
    let stage1_wasm = sigil_compiler::compile_tool(&stage1_tool)
        .expect("the stage-1 tool compiles")
        .wasm;
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        &stage1_wasm,
        input.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("stage-1 completes under the SELF-4 budget");
    let shex = String::from_utf8_lossy(&result.output).into_owned();
    assert!(!shex.contains("!!"), "stage-1 must emit poison-free");
    assert_eq!(
        shex.len(),
        ohex.len(),
        "BOOT-SELF: Stage-1 and Stage-2 module sizes match"
    );
    assert_eq!(shex, ohex, "BOOT-SELF: Stage-1 == Stage-2, byte for byte");
    assert_eq!(
        shex.len() / 2,
        PIN_STAGE1_CAP0_MODULE_BYTES,
        "PIN-1 (Stage-1 side): the SELFHOST-emitted cap0 module is {} B, pinned \
         {PIN_STAGE1_CAP0_MODULE_BYTES}. The equality above is RELATIONAL — it stays green when \
         both stages move together. This pin is the absolute lock on the selfhost side and must be \
         repinned with its own stated reason (SC-P1: pin the measured value).",
        shex.len() / 2
    );
}

// ── Stage-3-A: the executable closure — the runnable library + the fixed point ──────────────
//
// Stage-3-0 certified the compiler as a driver-LESS LIBRARY (`cap0_input`, cut at `tool_main`):
// byte-identical selfhost-emit, but no entry point (`NoEntryPoint` if run). Stage-3-A turns that
// static byte-identity into an EXECUTABLE self-reproducing fixed point by (a) extending the
// library with a poison-free pipeline ENTRY (`run_from_str`) that the selfhost still emits
// byte-identically, and (b) splicing a tiny raw-glue `tool_main` into the SIGIL-emitted module so
// it RUNS and reproduces itself. The oracle contributes only the fixed glue; all code-generation
// is the SIGIL-emitted library. Contract: docs/specs/stage3-thompson-closure.md.

/// The runnable-library entry (Stage-3-A LIB). `run_from_str` is the pipeline driver MINUS the
/// Option-based input read (`from_bytes`/`unwrap_or`, which the sentinel-style selfhost cannot
/// emit) — so it is poison-free and the selfhost W-lane emits it byte-identically. It creates
/// `Arena::new()`/`Vec::new()` INTERNALLY (so those constructors are instantiated inside the
/// library, never needed as exports), and returns the packed module hex via `as_output`. It uses
/// `ai_encode_wasm` (the raw module-hex emit), matching the byte capstone's emit path exactly.
fn run_from_str_entry() -> &'static str {
    concat!(
        "pub fn run_from_str(src: str) -> i64 {\n",
        "    let toks: Vec<Token> = lex(src);\n",
        "    let mut nodes: Arena<PNode> = Arena::new();\n",
        "    let mut kids: Vec<i64> = Vec::new();\n",
        "    let root: i64 = parser_parse(src, toks, nodes, kids);\n",
        "    let e: i64 = mn_expand(nodes, kids, root);\n",
        "    let hex: str = ai_encode_wasm(nodes, kids, root);\n",
        "    return hex.as_output();\n",
        "}\n",
    )
}

/// `cap0_input` extended with `run_from_str` (Stage-3-A LIB, "cap0'"). The entry is inserted at
/// the END of `module tool` (right before `module string;`) so its unqualified pipeline calls
/// (`lex`/`parser_parse`/`mn_expand`/`ai_encode_wasm`) resolve in-module. (Qualified cross-module
/// `tool::lex(...)` is rejected by the oracle — falsified in Phase-0 — so an in-module entry is
/// the only shape that both resolves and leaves the library's function layout byte-identical.)
fn cap0_input_runnable() -> String {
    let cap = cap0_input();
    let marker = "\nmodule string;";
    let idx = cap
        .find(marker)
        .expect("string module present in cap0_input");
    format!("{}\n{}{}", &cap[..idx], run_from_str_entry(), &cap[idx..])
}

/// Stage-3-A LIB gate: the runnable library `cap0'` is emitted poison-FREE. `run_from_str` adds
/// no poisoned fn to the certified surface (the precondition for byte-identity). Mirrors
/// `cap0_poison_census_ratchet` over the runnable input.
#[test]
fn cap0_runnable_poison_census_zero() {
    let input = cap0_input_runnable();
    let census_tool = {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);
         let src: str = opt.unwrap_or(\"\");
         let toks: Vec<Token> = lex(src);
         let mut nodes: Arena<PNode> = Arena::new();
         let mut kids: Vec<i64> = Vec::new();
         let root: i64 = parser_parse(src, toks, nodes, kids);
         let e: i64 = mn_expand(nodes, kids, root);
         let census: str = ai_wasm_poison_census(nodes, kids, root);
         return census.as_output();";
        boot_mono_tool(body)
    };
    let census_wasm = sigil_compiler::compile_tool(&census_tool)
        .expect("the census tool compiles")
        .wasm;
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        &census_wasm,
        input.as_bytes(),
        3_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the census executes under the SELF-4 budget");
    let out = String::from_utf8_lossy(&result.output).into_owned();
    let names: Vec<&str> = out.split(';').filter(|s| !s.is_empty()).collect();
    assert_eq!(
        names.len(),
        0,
        "run_from_str must not poison the certified library (first: {:?})",
        &names[..names.len().min(10)]
    );
}

/// Stage-3-A LIB capstone: the RUNNABLE library self-certifies byte-identically. Stage-1 (the
/// selfhost compiler-as-wasm, `ai_encode_wasm` over `cap0'`) emits a whole-module hex IDENTICAL
/// to Stage-2 (the Rust oracle). So extending the certified library with the runnable pipeline
/// entry preserves the boot self-certification — the foundation for the executable closure.
#[test]
fn boot_self_runnable_byte_capstone() {
    let input = cap0_input_runnable();
    let (okind, _, ohex) = split_protocol(&oracle_compile("boot_self_runnable", &input));
    assert_eq!(okind, "OK", "Stage-2 exists for the runnable library");
    let stage1_tool = {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);
         let src: str = opt.unwrap_or(\"\");
         let toks: Vec<Token> = lex(src);
         let mut nodes: Arena<PNode> = Arena::new();
         let mut kids: Vec<i64> = Vec::new();
         let root: i64 = parser_parse(src, toks, nodes, kids);
         let e: i64 = mn_expand(nodes, kids, root);
         let hex: str = ai_encode_wasm(nodes, kids, root);
         return hex.as_output();";
        boot_mono_tool(body)
    };
    let stage1_wasm = sigil_compiler::compile_tool(&stage1_tool)
        .expect("the stage-1 tool compiles")
        .wasm;
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        &stage1_wasm,
        input.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("stage-1 completes under the SELF-4 budget");
    let shex = String::from_utf8_lossy(&result.output).into_owned();
    assert!(!shex.contains("!!"), "stage-1 must emit poison-free");
    assert_eq!(
        shex.len(),
        ohex.len(),
        "Stage-1 and Stage-2 module sizes match for the runnable library"
    );
    assert_eq!(
        shex, ohex,
        "Stage-3-A LIB: Stage-1 == Stage-2, byte for byte (runnable library)"
    );
    assert_eq!(
        shex.len() / 2,
        PIN_STAGE1_RUNNABLE_MODULE_BYTES,
        "PIN-1 (Stage-1 side): the SELFHOST-emitted runnable-library module is {} B, pinned \
         {PIN_STAGE1_RUNNABLE_MODULE_BYTES}",
        shex.len() / 2
    );
}

/// Stage-1 as WASM: the selfhost compiler (lex → parse → mn_expand → `ai_encode_wasm`) compiled
/// by the oracle. Running it on a source string yields the SELFHOST-emitted module hex — the
/// SIGIL-built code-generation logic, no oracle in the emit path.
fn selfhost_emit_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);
         let src: str = opt.unwrap_or(\"\");
         let toks: Vec<Token> = lex(src);
         let mut nodes: Arena<PNode> = Arena::new();
         let mut kids: Vec<i64> = Vec::new();
         let root: i64 = parser_parse(src, toks, nodes, kids);
         let e: i64 = mn_expand(nodes, kids, root);
         let hex: str = ai_encode_wasm(nodes, kids, root);
         return hex.as_output();";
        sigil_compiler::compile_tool(&boot_mono_tool(body))
            .expect("the stage-1 tool compiles")
            .wasm
    })
}

/// Run the SELFHOST compiler-as-wasm on `input`, returning the emitted module hex.
fn selfhost_emit(input: &str) -> String {
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        selfhost_emit_wasm(),
        input.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("stage-1 completes under the SELF-4 budget");
    String::from_utf8_lossy(&result.output).into_owned()
}

fn unhex(hex: &str) -> Vec<u8> {
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).expect("valid hex"))
        .collect()
}

fn push_uleb(mut v: u32, out: &mut Vec<u8>) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            break;
        }
        out.push(byte | 0x80);
    }
}

/// Decode an unsigned LEB128 at `data[pos..]`, returning (value, next_pos).
fn read_uleb(data: &[u8], mut pos: usize) -> (u32, usize) {
    let mut result = 0u32;
    let mut shift = 0;
    loop {
        let byte = data[pos];
        pos += 1;
        result |= ((byte & 0x7f) as u32) << shift;
        if byte & 0x80 == 0 {
            break;
        }
        shift += 7;
    }
    (result, pos)
}

/// The semantic facts the splice needs from the SIGIL-emitted module: the absolute function
/// index of the exported `run_from_str`, the `BUMP_PTR` global index, the count of imported
/// functions, and the type/function-section counts (to compute the new indices).
fn splice_info(module: &[u8]) -> (u32, u32, u32, u32, u32) {
    use wasmparser::{ExternalKind, Imports, Parser, Payload, TypeRef};
    let mut rfs = None;
    let mut bump = None;
    let mut num_imported_funcs = 0u32;
    let mut type_count = 0u32;
    let mut func_count = 0u32;
    for payload in Parser::new(0).parse_all(module) {
        match payload.expect("valid wasm module") {
            Payload::ImportSection(r) => {
                for group in r {
                    // SIGIL emits standard (non-compact) imports → one `Single` per import.
                    match group.expect("import group") {
                        Imports::Single(_, import) => {
                            if matches!(import.ty, TypeRef::Func(_)) {
                                num_imported_funcs += 1;
                            }
                        }
                        _ => panic!("unexpected compact import encoding in a SIGIL module"),
                    }
                }
            }
            Payload::TypeSection(r) => type_count = r.count(),
            Payload::FunctionSection(r) => func_count = r.count(),
            Payload::ExportSection(r) => {
                for e in r {
                    let e = e.expect("export");
                    if e.kind == ExternalKind::Func && e.name.contains("run_from_str") {
                        rfs = Some(e.index);
                    }
                    if e.kind == ExternalKind::Global && e.name == "BUMP_PTR" {
                        bump = Some(e.index);
                    }
                }
            }
            _ => {}
        }
    }
    (
        rfs.expect("the module exports run_from_str"),
        bump.expect("the module exports BUMP_PTR"),
        num_imported_funcs,
        type_count,
        func_count,
    )
}

/// Splice a fixed raw-glue `tool_main` into a SIGIL-emitted module (Stage-3-A closure). The new
/// function — appended as the LAST function so NO existing index shifts — is pure I/O glue: it
/// builds an 8-byte `str` header `{data_ptr@0, len@4}` from the runtime's `(input_ptr,
/// input_len)`, then tail-calls the library's own `run_from_str`. It contains no compiler logic
/// (exactly one `call`, to `run_from_str`); all code-generation stays in the SIGIL-emitted
/// library. Sections are rebuilt by hand (append-one-entry to Type/Function/Export/Code), every
/// other section copied verbatim — a dumb, deterministic transform (X-WRAP: byte-constant).
fn splice_runnable_entry(module: &[u8]) -> Vec<u8> {
    let (rfs_func, bump_global, num_imported_funcs, type_count, func_count) = splice_info(module);
    let new_func_index = num_imported_funcs + func_count;
    let new_type_index = type_count;

    // The glue body: locals = [i32 hdr]; then the fixed ~14-op sequence.
    // locals declaration: 1 group of (1 x i32) — the `hdr` local
    let mut code = vec![0x01, 0x01, 0x7f];
    // hdr = BUMP_PTR; BUMP_PTR += 8
    code.push(0x23);
    push_uleb(bump_global, &mut code); // global.get BUMP_PTR
    code.extend_from_slice(&[0x22, 0x02]); // local.tee $hdr
    code.extend_from_slice(&[0x41, 0x08]); // i32.const 8
    code.push(0x6a); // i32.add
    code.push(0x24);
    push_uleb(bump_global, &mut code); // global.set BUMP_PTR
    // hdr[0] = (u32) input_ptr
    code.extend_from_slice(&[0x20, 0x02]); // local.get $hdr
    code.extend_from_slice(&[0x20, 0x00]); // local.get 0 (ptr)
    code.extend_from_slice(&[0x36, 0x02, 0x00]); // i32.store align=2 offset=0
    // hdr[4] = (u32) input_len
    code.extend_from_slice(&[0x20, 0x02]); // local.get $hdr
    code.extend_from_slice(&[0x20, 0x01]); // local.get 1 (len)
    code.extend_from_slice(&[0x36, 0x02, 0x04]); // i32.store align=2 offset=4
    // run_from_str(hdr) -> i64  (returned)
    code.extend_from_slice(&[0x20, 0x02]); // local.get $hdr
    code.push(0x10);
    push_uleb(rfs_func, &mut code); // call run_from_str
    code.push(0x0b); // end

    let mut code_entry = Vec::new();
    push_uleb(code.len() as u32, &mut code_entry);
    code_entry.extend_from_slice(&code);

    // (i32, i32) -> i64
    let type_entry = vec![0x60, 0x02, 0x7f, 0x7f, 0x01, 0x7e];
    let mut func_entry = Vec::new();
    push_uleb(new_type_index, &mut func_entry);
    let name = b"tool__tool_main";
    let mut export_entry = Vec::new();
    push_uleb(name.len() as u32, &mut export_entry);
    export_entry.extend_from_slice(name);
    export_entry.push(0x00); // func kind
    push_uleb(new_func_index, &mut export_entry);

    // append one entry to a section's [count][entries...] content
    let append = |content: &[u8], entry: &[u8]| -> Vec<u8> {
        let (count, off) = read_uleb(content, 0);
        let mut out = Vec::new();
        push_uleb(count + 1, &mut out);
        out.extend_from_slice(&content[off..]);
        out.extend_from_slice(entry);
        out
    };

    let mut out = Vec::new();
    out.extend_from_slice(&module[0..8]); // magic + version
    let mut pos = 8;
    while pos < module.len() {
        let id = module[pos];
        pos += 1;
        let (size, off) = read_uleb(module, pos);
        pos = off;
        let content = &module[pos..pos + size as usize];
        pos += size as usize;
        let new_content = match id {
            1 => append(content, &type_entry),   // Type
            3 => append(content, &func_entry),   // Function
            7 => append(content, &export_entry), // Export
            10 => append(content, &code_entry),  // Code
            _ => content.to_vec(),
        };
        out.push(id);
        push_uleb(new_content.len() as u32, &mut out);
        out.extend_from_slice(&new_content);
    }
    out
}

/// Count the `call` operators in the LAST defined function of a module (the spliced tool_main).
/// SC-2 (wrapper is glue): exactly one, targeting run_from_str.
fn last_fn_calls(module: &[u8]) -> Vec<u32> {
    use wasmparser::{Operator, Parser, Payload};
    let mut bodies = Vec::new();
    for payload in Parser::new(0).parse_all(module) {
        if let Payload::CodeSectionEntry(body) = payload.expect("valid wasm") {
            bodies.push(body);
        }
    }
    let last = bodies.last().expect("at least one function");
    let mut calls = Vec::new();
    for op in last.get_operators_reader().expect("ops").into_iter() {
        if let Operator::Call { function_index } = op.expect("op") {
            calls.push(function_index);
        }
    }
    calls
}

/// Stage-3-A RED gate: the bare SIGIL-emitted library is NOT runnable — it has no `tool_main`
/// entry point (it was certified driver-less). Running it fails loudly with `NoEntryPoint`.
#[test]
fn stage3a_bare_library_has_no_entry() {
    let shex = selfhost_emit(&cap0_input_runnable());
    let bytes = unhex(&shex);
    let err = sigil_runtime::execute_ephemeral(
        &bytes,
        cap0_input_runnable().as_bytes(),
        1_000_000,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect_err("the bare library must have no entry point");
    let msg = err.to_string();
    assert!(
        msg.contains("entry point"),
        "expected NoEntryPoint, got: {msg}"
    );
}

/// Stage-3-A THE EXECUTABLE CLOSURE. Take the SELFHOST-emitted runnable library (`shex' =
/// selfhost-emit(cap0')`), splice a fixed raw-glue `tool_main`, and RUN it on `cap0'` — its
/// `run_from_str` (the SIGIL-built code-generation logic) re-emits the whole module, reproducing
/// `shex'` byte-for-byte. The oracle contributed only the fixed glue; the fixed point is live:
/// a compiler whose emit logic is SIGIL-built, executed, reproduces itself.
#[test]
fn stage3a_executable_closure() {
    let input = cap0_input_runnable();
    // shex' = the SELFHOST-emitted runnable library (no oracle in the emit path).
    let shex_prime = selfhost_emit(&input);
    assert!(!shex_prime.contains("!!"), "shex' must be poison-free");
    let shex_bytes = unhex(&shex_prime);

    // Splice determinism (X-WRAP): the glue is byte-constant.
    let runnable = splice_runnable_entry(&shex_bytes);
    assert_eq!(
        runnable,
        splice_runnable_entry(&shex_bytes),
        "the splice is deterministic"
    );

    // SC-2: the spliced tool_main is pure glue — exactly one call, to run_from_str.
    let (rfs_func, _, _, _, _) = splice_info(&shex_bytes);
    let calls = last_fn_calls(&runnable);
    assert_eq!(
        calls,
        vec![rfs_func],
        "the wrapper must contain exactly one call (to run_from_str), no compiler logic"
    );

    // RUN the SIGIL-built compiler on its own source → reproduce shex'.
    let out = sigil_runtime::execute_ephemeral_with_memory_budget(
        &runnable,
        input.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the spliced runnable executes under the SELF-4 budget");
    let reproduced = String::from_utf8_lossy(&out.output).into_owned();

    assert!(
        !reproduced.contains("!!"),
        "the reproduction must be poison-free"
    );
    assert_eq!(
        reproduced.len(),
        shex_prime.len(),
        "closure size mismatch: reproduced {} vs shex' {}",
        reproduced.len(),
        shex_prime.len()
    );
    assert_eq!(
        reproduced, shex_prime,
        "STAGE-3-A CLOSURE: run(splice(shex'), cap0') == shex', byte for byte"
    );
}

// ── Stage-3-B: the trusting-trust defense (Diverse Double-Compiling) demonstration ──────────
//
// Thompson (1984): a compiler can carry a self-perpetuating backdoor that survives removal from
// source. Wheeler's Diverse Double-Compiling (2009) is the defense: compile the compiler's source
// with a SECOND, independent trusted compiler; if the result is bit-identical to the self-compiled
// binary, no trusting-trust payload is present. SIGIL's byte-identity capstone IS that DDC check
// (the Rust oracle vs the selfhost). Stage-3-B demonstrates the defense working: an honest selfhost
// gives a clean bill (byte-identical), while a backdoored variant A′ — which injects a benign
// marker gated on recognizing its OWN source — is CAUGHT (its self-emission diverges from the
// oracle). Contract: docs/specs/stage3-thompson-closure.md.

/// A benign, obviously-identifiable payload (AG-3): a valid WASM custom section named "thompson"
/// with empty data. `00`=custom-section id, `09`=section size, `08`=name length,
/// `74686f6d70736f6e`="thompson". Appended at the module end, it is ignored by execution (the
/// module stays valid + runnable) but changes the bytes — so the DDC catches it.
const THOMPSON_MARKER_HEX: &str = "00090874686f6d70736f6e";

/// A′ — the BACKDOORED selfhost compiler. Identical to the honest Stage-1 emit lane, except it
/// appends `THOMPSON_MARKER_HEX` to its output IFF it recognizes the source is its own LIB (the
/// source contains the compiler-unique fn name `ai_wasm_poison_census`). This is the trusting-trust
/// payload: self-recognizing, gated, benign. It is oracle-compiled (A′'s own source passes all 7
/// gates); the backdoor lives in A′'s emit lane, exactly where Thompson's would.
fn a_prime_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);
         let src: str = opt.unwrap_or(\"\");
         let toks: Vec<Token> = lex(src);
         let mut nodes: Arena<PNode> = Arena::new();
         let mut kids: Vec<i64> = Vec::new();
         let root: i64 = parser_parse(src, toks, nodes, kids);
         let e: i64 = mn_expand(nodes, kids, root);
         let hex: str = ai_encode_wasm(nodes, kids, root);
         let is_self: bool = src.contains(\"ai_wasm_poison_census\");
         let mut marked: str = hex;
         if is_self {
             marked = hex.concat(\"00090874686f6d70736f6e\");
         }
         return marked.as_output();";
        sigil_compiler::compile_tool(&boot_mono_tool(body))
            .expect("the backdoored A' tool compiles (passes all 7 gates)")
            .wasm
    })
}

/// Run the BACKDOORED compiler A′ on `input`, returning the emitted module hex.
fn a_prime_emit(input: &str) -> String {
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        a_prime_wasm(),
        input.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("A' completes under the SELF-4 budget");
    String::from_utf8_lossy(&result.output).into_owned()
}

/// Execute the COMMITTED SEED on `src` — the DDC's second compiler. The distinction from
/// `oracle_compile` is the whole point of the seed edition below: no Rust compiler code runs
/// here. The seed is a frozen WASM binary written in SIGIL; the only Rust in this path is the
/// sandbox that executes it. (The seed is the GATED artifact, so its output is protocol-shaped.)
fn seed_compile(src: &str) -> String {
    let seed = read_seed();
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        &seed,
        src.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the committed seed executes as the DDC's second compiler");
    String::from_utf8_lossy(&result.output).into_owned()
}

/// Stage-3-B THE DEFENSE: the DDC clears the honest compiler and CATCHES the backdoored one. The
/// honest selfhost self-emits byte-identical to the oracle (clean bill); A′ diverges (caught), by
/// exactly the benign marker — and the marked module still passes as valid WASM (a real, working
/// backdoor, not a broken build). This is the trusting-trust defense demonstrated end to end.
#[test]
fn stage3b_ddc_honest_passes_backdoored_caught() {
    let input = cap0_input_runnable();
    let (okind, _, ohex) = split_protocol(&oracle_compile("stage3b_oracle", &input));
    assert_eq!(
        okind, "OK",
        "the oracle (DDC's trusted second compiler) accepts cap0'"
    );

    // The honest selfhost gets a CLEAN bill — byte-identical to the oracle.
    let honest = selfhost_emit(&input);
    assert_eq!(
        honest, ohex,
        "DDC: the honest selfhost self-emits byte-identically to the oracle (no payload)"
    );

    // A′ is CAUGHT — its self-emission diverges from the oracle.
    let backdoored = a_prime_emit(&input);
    assert_ne!(
        backdoored, ohex,
        "DDC: the backdoored A' must NOT be byte-identical (the defense catches it)"
    );
    // ...and the divergence is exactly the benign, identifiable marker.
    assert_eq!(
        backdoored,
        format!("{ohex}{THOMPSON_MARKER_HEX}"),
        "the divergence is exactly the benign thompson marker (AG-3)"
    );

    // A′ passes the 7 gates AND its output is a valid runnable module (a real backdoor).
    let bytes = unhex(&backdoored);
    assert!(
        wasmtime::Module::new(&wasmtime::Engine::default(), &bytes).is_ok(),
        "the backdoored module must still be valid WASM (passes gates, runs)"
    );
}

/// Stage-3-B: the backdoor is TARGETED — A′ recognizes only its own LIB. On a foreign program
/// (which does not contain the self-signature) A′ emits honestly, byte-identical to the oracle. A
/// self-recognizing payload that fired on every input would be trivially detectable; Thompson's
/// (and this) fires only on the recognized target.
#[test]
fn stage3b_backdoor_targets_only_self() {
    let foreign =
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n";
    let (okind, _, oforeign) = split_protocol(&oracle_compile("stage3b_foreign", foreign));
    assert_eq!(okind, "OK", "the oracle accepts the foreign program");
    let a_foreign = a_prime_emit(foreign);
    assert_eq!(
        a_foreign, oforeign,
        "A' emits a foreign (non-self) program honestly — the backdoor does not fire"
    );
    assert!(
        !a_foreign.ends_with(THOMPSON_MARKER_HEX),
        "no marker on a foreign program"
    );
}

/// Stage-3-B: the marker SURVIVES a generation — the backdoored compiler A′ produces a valid,
/// working next-generation compiler (marker present in the emitted binary; that binary still
/// compiles). We splice a runnable entry into the marked module and RUN it on a foreign program;
/// it emits a valid module. (Honest scope: this benign marker is PASSIVE — the gen-2 output is
/// itself clean, i.e. the payload does not self-reproduce into gen-2. Full self-perpetuating
/// propagation across N generations is the weaponized quine, an explicit anti-goal — AG-2/AG-3.)
#[test]
fn stage3b_backdoored_compiler_still_functions() {
    let backdoored = a_prime_emit(&cap0_input_runnable());
    assert!(
        backdoored.ends_with(THOMPSON_MARKER_HEX),
        "the marker survived into the gen-1 compiler binary"
    );
    let runnable = splice_runnable_entry(&unhex(&backdoored));
    let foreign =
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n";
    let (_, _, oforeign) = split_protocol(&oracle_compile("stage3b_gen2", foreign));
    let out = sigil_runtime::execute_ephemeral_with_memory_budget(
        &runnable,
        foreign.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the backdoored compiler executes as a runnable tool");
    let gen2 = String::from_utf8_lossy(&out.output).into_owned();
    assert_eq!(
        gen2, oforeign,
        "the backdoored compiler is a functioning compiler (gen-2 output is valid + honest)"
    );
}

// ── Stage-3-B, SEED EDITION: the second compiler is not the oracle ───────────────────────────
//
// HB-3's controlling objection to the tests above was CIRCULARITY: the "independent" second
// compiler judging the DDC comparison WAS the Rust oracle, so a Thompson backdoor in the oracle
// would sit on both sides of every equality. The committed seed (claim 38) removes the oracle
// from the comparison — it is a frozen SIGIL-written binary that compiles the DDC input itself.
//
// What this does NOT establish, and cannot: the GENESIS seed was oracle-built
// (seed/PROVENANCE.md), so a backdoor already present in the oracle at freeze time would have
// been baked into the seed and the two would still agree. The bound moves from circularity to
// TIME — post-freeze divergence is detectable, pre-freeze compromise is not.

/// The DDC verdict delivered BY THE SEED: the honest selfhost emitter gets a clean bill, and the
/// backdoored A′ is caught — by exactly the benign marker.
///
/// PRECISELY what "the oracle is absent" means here, because the looser reading is an overclaim.
/// Both compared VALUES are computed by SIGIL code-generation running as WASM, and no
/// `oracle_compile` call adjudicates. But the honest side's BINARY is still built by
/// `sigil_compiler::compile_tool` at test time (so is A′'s) — that is the bootstrap role HB-2
/// keeps for Rust. The seed side has no rustc involvement at verdict time at all: it is committed
/// bytes. So the comparison is a FROZEN SIGIL compiler against a FRESHLY-BUILT one, which is
/// exactly the axis that detects post-freeze change — and is not an oracle-free pipeline.
#[test]
fn stage3b_ddc_second_compiler_is_the_seed() {
    let input = cap0_input_runnable();
    let (kind, stage, seed_hex) = split_protocol(&seed_compile(&input));
    assert_eq!(
        (kind.as_str(), stage.as_str()),
        ("OK", ""),
        "the seed's own gate chain must accept the DDC input (first reject: {})",
        seed_hex.chars().take(200).collect::<String>()
    );
    assert!(
        !seed_hex.is_empty() && !seed_hex.contains("!!"),
        "the seed's emit must be non-empty and poison-free"
    );

    // The honest selfhost gets a CLEAN BILL from the seed — oracle not consulted.
    let honest = selfhost_emit(&input);
    assert_eq!(
        honest, seed_hex,
        "DDC (seed edition): the honest selfhost agrees with the frozen seed byte-for-byte"
    );

    // A′ is CAUGHT by the seed — oracle not consulted.
    let backdoored = a_prime_emit(&input);
    assert_ne!(
        backdoored, seed_hex,
        "DDC (seed edition): the backdoored A' must diverge from the frozen seed"
    );
    assert_eq!(
        backdoored,
        format!("{seed_hex}{THOMPSON_MARKER_HEX}"),
        "…and the divergence is exactly the benign thompson marker"
    );
}

/// The DDC conclusion stated directly: two compilers of DIFFERENT PROVENANCE — the Rust oracle
/// (hand-written, compiled by rustc) and the frozen SIGIL seed (written in SIGIL, executing as
/// WASM) — produce the same bytes for the same source. A divergence introduced after the freeze,
/// on either side, breaks this equality. A backdoor invisible to it would have to be present in
/// both, which for the seed means present in the oracle BEFORE the genesis freeze — the bound
/// HB-3 now states.
#[test]
fn stage3b_seed_and_oracle_agree_on_the_ddc_input() {
    let input = cap0_input_runnable();
    let (okind, _, ohex) = split_protocol(&oracle_compile("stage3b_seed_agree", &input));
    assert_eq!(okind, "OK", "the oracle accepts the DDC input");
    let (skind, _, shex) = split_protocol(&seed_compile(&input));
    assert_eq!(skind, "OK", "the seed accepts the DDC input");
    assert_eq!(
        shex, ohex,
        "DDC: the frozen seed and the Rust oracle agree byte-for-byte on the DDC input"
    );
    // SC-P4 anti-vacuity: the comparison must be able to SEE a difference. The backdoored A′ is
    // the live witness — same input, same comparison, different verdict.
    assert_ne!(
        a_prime_emit(&input),
        shex,
        "anti-vacuity: this equality is not trivially satisfiable — A' fails it"
    );
}

/// The complete with-driver `tool_main` self-certifies byte-identically through
/// the selfhost W-lane, without a Stage-3 splice.
#[test]
fn ag6_5_with_driver_byte_capstone() {
    let input = with_driver_input();
    let oracle = oracle_compile("ag6_5", &input);
    let (okind, _, ohex) = split_protocol(&oracle);
    assert_eq!(
        okind, "OK",
        "Stage-2 (oracle) accepts the with-driver source"
    );
    let stage1_tool = {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);
         let src: str = opt.unwrap_or(\"\");
         let toks: Vec<Token> = lex(src);
         let mut nodes: Arena<PNode> = Arena::new();
         let mut kids: Vec<i64> = Vec::new();
         let root: i64 = parser_parse(src, toks, nodes, kids);
         let e: i64 = mn_expand(nodes, kids, root);
         let hex: str = ai_encode_wasm(nodes, kids, root);
         return hex.as_output();";
        boot_mono_tool(body)
    };
    let stage1_wasm = sigil_compiler::compile_tool(&stage1_tool)
        .expect("the with-driver stage-1 tool compiles")
        .wasm;
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        &stage1_wasm,
        input.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("with-driver stage-1 completes under the SELF-4 budget");
    let shex = String::from_utf8_lossy(&result.output).into_owned();
    assert!(
        !shex.contains("!!"),
        "AG6-5: the with-driver tool_main must emit POISON-FREE"
    );
    assert_eq!(
        shex.len(),
        ohex.len(),
        "AG6-5: with-driver Stage-1 and Stage-2 module sizes match"
    );
    assert_eq!(
        shex, ohex,
        "AG6-5: the with-driver tool_main self-certifies BYTE-IDENTICALLY (the Stage-3 splice is retired)"
    );
    assert_eq!(
        shex.len() / 2,
        PIN_STAGE1_WITH_DRIVER_MODULE_BYTES,
        "PIN-1 (Stage-1 side): the SELFHOST-emitted with-driver module is {} B, pinned \
         {PIN_STAGE1_WITH_DRIVER_MODULE_BYTES}",
        shex.len() / 2
    );

    // The with-driver artifact was previously asserted ONLY as a hex string equal to another hex
    // string — nothing established that the agreed-upon bytes are a WASM module at all. Both
    // stages could have emitted identical GARBAGE and every capstone stayed green. Constructing it
    // proves it validates AND compiles. Its EXECUTION is a separate matter, asserted separately:
    // `hb1_stub_free_executable_fixed_point` runs this artifact on its own source (claims 36-37).
    let engine = wasmtime::Engine::default();
    let module_bytes = unhex(&shex);
    assert!(
        wasmtime::Module::new(&engine, &module_bytes).is_ok(),
        "AG6-5: the self-certified with-driver module must be valid, compilable WASM — \
         byte-identity between two emitters says nothing about whether either emitted a module"
    );

    // SC-P4 anti-stub: the assertion above is "the instrument said yes", which is worthless if the
    // instrument says yes to everything. Two mutants that are invalid BY CONSTRUCTION — a broken
    // magic header, and a module whose final section is one byte shorter than its own length
    // prefix declares — must both be rejected.
    let mut bad_magic = module_bytes.clone();
    bad_magic[0] ^= 0xFF;
    assert!(
        wasmtime::Module::new(&engine, &bad_magic).is_err(),
        "anti-stub: a corrupted WASM magic header must be REJECTED"
    );
    let truncated = &module_bytes[..module_bytes.len() - 1];
    assert!(
        wasmtime::Module::new(&engine, truncated).is_err(),
        "anti-stub: a module truncated inside its final section must be REJECTED"
    );
}

// ── Certified artifact preservation: PIN-1 / PIN-2 ────────────────────────────────────────────
//
// Relational capstones can miss changes when both stages move together. These
// absolute pins make certified-surface movement an explicit, reviewed change.
const PIN_CAP0_SRC_CHARS: usize = 1_150_219;
const PIN_CAP0_MODULE_BYTES: usize = 454_099;
const PIN_CAP0_RUNNABLE_SRC_CHARS: usize = 1_150_574;
const PIN_CAP0_RUNNABLE_MODULE_BYTES: usize = 454_453;
const PIN_WITH_DRIVER_SRC_CHARS: usize = 1_151_054;
const PIN_WITH_DRIVER_MODULE_BYTES: usize = 454_798;
// PIN-1, STAGE-1 SIDE. The six pins above measure the ORACLE's output: `pin_module_bytes` calls
// `oracle_compile`, so Stage-1's own size was pinned only TRANSITIVELY — via the capstones'
// `shex == ohex`. That chain has two links, and a weakened or deleted equality assertion breaks
// it silently: Stage-1 could then emit any size at all with no pin objecting. These three pin the
// SELFHOST-emitted module directly, at the point each capstone already holds `shex`, so the
// selfhost side costs no extra Stage-1 run. They must be repinned on their own, with their own
// stated reason, even when the oracle pins move with them.
const PIN_STAGE1_CAP0_MODULE_BYTES: usize = 454_099;
const PIN_STAGE1_RUNNABLE_MODULE_BYTES: usize = 454_453;
const PIN_STAGE1_WITH_DRIVER_MODULE_BYTES: usize = 454_798;
// Catastrophic-shrink floors (SC-P3): these survive a lazy "edit the exact pin down" change.
const PIN_FLOOR_SRC_CHARS: usize = 1_000_000;
const PIN_FLOOR_MODULE_BYTES: usize = 400_000;

/// Build the library, `run_from_str` entry, and real `tool_main` measured by
/// both the capstone and its absolute pins.
///
/// UNIFICATION: the driver body IS `sh_mono_body` — ingestion, then lex → parse → mn_expand →
/// `sh_compile` (all seven gates, short-circuiting) → the frozen protocol via `as_output`. The
/// previous driver called `run_from_str` (the emit lane only), which left HB-1's residue: the
/// gates were byte-certified but not in the artifact's own executed body. `run_from_str` stays
/// in the artifact (the runnable capstone's entry, and the nesting cap0 ⊂ runnable ⊂ with-driver
/// is preserved); `tool_main` simply no longer routes around the gates.
fn with_driver_input() -> String {
    let cap = cap0_input();
    let marker = "\nmodule string;";
    let idx = cap
        .find(marker)
        .expect("string module present in cap0_input");
    let driver = concat!(
        "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n",
        "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n",
        "    let src: str = opt.unwrap_or(\"\");\n",
        "    let toks: Vec<Token> = lex(src);\n",
        "    let mut nodes: Arena<PNode> = Arena::new();\n",
        "    let mut kids: Vec<i64> = Vec::new();\n",
        "    let root: i64 = parser_parse(src, toks, nodes, kids);\n",
        "    let e: i64 = mn_expand(nodes, kids, root);\n",
        "    let out: str = sh_compile(nodes, kids, root);\n",
        "    return out.as_output();\n",
        "}\n",
    );
    format!(
        "{}\n{}\n{}{}",
        &cap[..idx],
        run_from_str_entry(),
        driver,
        &cap[idx..]
    )
}

fn pin_module_bytes(label: &str, src: &str) -> usize {
    let (kind, _, ohex) = split_protocol(&oracle_compile(label, src));
    assert_eq!(
        kind, "OK",
        "PIN: the oracle must accept the certified input `{label}`"
    );
    ohex.len() / 2
}

/// PIN-1: the certified artifact's ABSOLUTE size — exact pins plus catastrophic-shrink floors.
/// Without this, shrinking `cap0_input` (e.g. adding a name to the strip list) moves BOTH sides
/// of every byte capstone and CI never notices the achievement got smaller.
#[test]
fn pin_certified_artifact_size() {
    let cap = cap0_input();
    let capr = cap0_input_runnable();
    let wd = with_driver_input();

    // Floors first: these must hold even if someone edited an exact pin downward.
    for (label, chars) in [
        ("cap0", cap.len()),
        ("cap0_runnable", capr.len()),
        ("with_driver", wd.len()),
    ] {
        assert!(
            chars >= PIN_FLOOR_SRC_CHARS,
            "PIN-1 FLOOR: {label} source collapsed to {chars} chars (floor {PIN_FLOOR_SRC_CHARS}) \
             — the certified surface shrank catastrophically"
        );
    }

    let cap_bytes = pin_module_bytes("pin_cap0", &cap);
    let capr_bytes = pin_module_bytes("pin_cap0_runnable", &capr);
    let wd_bytes = pin_module_bytes("pin_with_driver", &wd);
    for (label, bytes) in [
        ("cap0", cap_bytes),
        ("cap0_runnable", capr_bytes),
        ("with_driver", wd_bytes),
    ] {
        assert!(
            bytes >= PIN_FLOOR_MODULE_BYTES,
            "PIN-1 FLOOR: {label} module collapsed to {bytes} B (floor {PIN_FLOOR_MODULE_BYTES})"
        );
    }

    // Report every drift together: all six values move when the certified source changes, and a
    // first-failure-only assertion turns a deliberate repin into six expensive capstone runs.
    let measurements = [
        ("cap0 source chars", cap.len(), PIN_CAP0_SRC_CHARS),
        (
            "cap0_runnable source chars",
            capr.len(),
            PIN_CAP0_RUNNABLE_SRC_CHARS,
        ),
        (
            "with_driver source chars",
            wd.len(),
            PIN_WITH_DRIVER_SRC_CHARS,
        ),
        ("cap0 module bytes", cap_bytes, PIN_CAP0_MODULE_BYTES),
        (
            "cap0_runnable module bytes",
            capr_bytes,
            PIN_CAP0_RUNNABLE_MODULE_BYTES,
        ),
        (
            "with_driver module bytes",
            wd_bytes,
            PIN_WITH_DRIVER_MODULE_BYTES,
        ),
    ];
    let drift: Vec<String> = measurements
        .iter()
        .filter(|(_, actual, expected)| actual != expected)
        .map(|(label, actual, expected)| format!("{label}: actual {actual}, pinned {expected}"))
        .collect();
    assert!(
        drift.is_empty(),
        "PIN-1: certified artifact sizes moved:\n{}",
        drift.join("\n")
    );
}

/// PIN-2 (SC-P4): anti-vacuity for the W-emit poison censuses. `cap0_poison_census_ratchet` and
/// `cap0_runnable_poison_census_zero` both assert `count == 0` — meaningful ONLY if the instrument
/// can still return non-zero. If `ai_wasm_poison_census` regressed to returning "", `split(';')`
/// yields zero names and those tests would pass while checking nothing. So: feed a KNOWN-poisoning
/// construct (a 2+-binder-arm match — a fenced hole, docs/CLAIMS.md §E) and require the
/// census to NAME it.
#[test]
fn pin_census_anti_vacuity() {
    let cap = cap0_input();
    let marker = "\nmodule string;";
    let idx = cap
        .find(marker)
        .expect("string module present in cap0_input");
    let poisoning = concat!(
        "enum PinProbeE { Pa(i64), Pb(i64) }\n",
        "pub fn pin_poison_probe() -> i64 {\n",
        "    let p: PinProbeE = PinProbeE::Pa(3);\n",
        "    let mut r: i64 = 0;\n",
        "    match p { Pa(a) => { r = a; }, Pb(b) => { r = 0 - b; }, }\n",
        "    return r;\n",
        "}\n",
    );
    let input = format!("{}\n{}{}", &cap[..idx], poisoning, &cap[idx..]);

    let census_tool = {
        let body = "    let opt: Option<str> = input_ptr.from_bytes(input_len);
         let src: str = opt.unwrap_or(\"\");
         let toks: Vec<Token> = lex(src);
         let mut nodes: Arena<PNode> = Arena::new();
         let mut kids: Vec<i64> = Vec::new();
         let root: i64 = parser_parse(src, toks, nodes, kids);
         let e: i64 = mn_expand(nodes, kids, root);
         let census: str = ai_wasm_poison_census(nodes, kids, root);
         return census.as_output();";
        boot_mono_tool(body)
    };
    let census_wasm = sigil_compiler::compile_tool(&census_tool)
        .expect("the census tool compiles")
        .wasm;
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        &census_wasm,
        input.as_bytes(),
        3_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the census executes under the SELF-4 budget");
    let out = String::from_utf8_lossy(&result.output).into_owned();
    let names: Vec<&str> = out.split(';').filter(|s| !s.is_empty()).collect();

    assert!(
        !names.is_empty(),
        "PIN-2 ANTI-VACUITY: a KNOWN-poisoning construct (2+-binder-arm match) censused CLEAN. \
         The poison census instrument is broken or stubbed — every `census == 0` assertion in this \
         file is therefore vacuous and proves nothing."
    );
    assert!(
        names.contains(&"pin_poison_probe"),
        "PIN-2 ANTI-VACUITY: the census returned {} name(s) but did not name the deliberately \
         poisoned fn `pin_poison_probe`; got {:?}",
        names.len(),
        &names[..names.len().min(10)]
    );
}

// ── PIN-7: CONTENT digests ────────────────────────────────────────────────────────────────────
//
// Size pins miss count-preserving edits; source and oracle-module digests close
// that gap. A separate CR check gives line-ending skew a useful failure message.

fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::{Digest, Sha256};
    let mut h = Sha256::new();
    h.update(bytes);
    h.finalize().iter().map(|x| format!("{x:02x}")).collect()
}

/// The oracle-emitted module hex for a certified input (Stage-2 side).
fn oracle_module_hex(label: &str, src: &str) -> String {
    let (kind, _, ohex) = split_protocol(&oracle_compile(label, src));
    assert_eq!(
        kind, "OK",
        "PIN-7: the oracle must accept the certified input `{label}`"
    );
    ohex
}

/// Prove the digest helper against known vectors and a same-length mutation.
#[test]
fn pin7_digest_instrument_is_not_vacuous() {
    assert_eq!(
        sha256_hex(b""),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        "SHA-256 of the empty string is wrong — the digest instrument is broken"
    );
    assert_eq!(
        sha256_hex(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        "SHA-256 of \"abc\" is wrong — the digest instrument is broken"
    );
    assert_ne!(
        sha256_hex(b"module m; fn f() -> i64 { return 1; }"),
        sha256_hex(b"module m; fn f() -> i64 { return 2; }"),
        "the digest must distinguish two same-length inputs — otherwise it cannot detect the          count-preserving change it exists to catch"
    );
}

/// Pin certified source and module content, including count-preserving changes.
#[test]
fn pin_certified_artifact_digest() {
    let cap = cap0_input();
    let capr = cap0_input_runnable();
    let wd = with_driver_input();

    // SC-P4 anti-stub for the two guards below: both assert a count is ZERO, which passes
    // trivially if the counter can never be non-zero. Prove each sees its own defect first.
    assert_eq!(
        "a\r\nb".bytes().filter(|b| *b == 13).count(),
        1,
        "anti-stub: the carriage-return counter must see a CR"
    );
    assert_eq!(
        "\u{feff}module tool;".matches('\u{feff}').count(),
        1,
        "anti-stub: the BOM counter must see a byte-order mark"
    );

    // Diagnose byte-level checkout skew before reporting six unrelated digest mismatches.
    for (label, src) in [
        ("cap0", &cap),
        ("cap0_runnable", &capr),
        ("with_driver", &wd),
    ] {
        let crs = src.bytes().filter(|b| *b == 13).count();
        assert_eq!(
            crs, 0,
            "PIN-7: `{label}` contains {crs} carriage returns. The certified sources are committed              LF; a CRLF checkout changes every digest below. Fix the checkout (or add *.sigil to              .gitattributes with eol=lf) rather than re-pinning the digests."
        );
        // Sibling of the CR guard, and a measured incident rather than a hypothetical: a Windows
        // shell round-trip (PowerShell 5.1 `Set-Content -Encoding utf8` always prepends one) or an
        // editor "UTF-8 with BOM" save adds U+FEFF. `.gitattributes` normalizes line endings but
        // says NOTHING about a BOM, so it reaches the index intact. Counted anywhere in the string,
        // not just at the front: these sources are CONCATENATED from many `selfhost/*.sigil` files,
        // so a BOM on any component lands mid-source. Without this the symptom is an inscrutable
        // digest mismatch — the exact failure the CR guard above exists to pre-empt.
        let boms = src.matches('\u{feff}').count();
        assert_eq!(
            boms, 0,
            "PIN-7: `{label}` contains {boms} UTF-8 byte-order marks (U+FEFF). A BOM changes every \
             digest below and the §A character pins. Strip it from the offending source file \
             rather than re-pinning."
        );
    }

    // Source digests include the strip-list result.
    const PIN_CAP0_SRC_SHA256: &str =
        "0c2a3df3ebc428e25eebcf2d5082e254622fb616dda02de1a9aa800d67c0e7d3";
    const PIN_CAP0_RUNNABLE_SRC_SHA256: &str =
        "4db2018ae98cee2aadeef77fb715ccd7886def2244565ebde5c4f003986cf9a2";
    const PIN_WITH_DRIVER_SRC_SHA256: &str =
        "fa69ab5fc7bbd58dba180432fc49d8cc7b7eff29cfdfa48b9ffe38c00d0cdc94";

    // Module digests pin the absolute oracle output behind relational capstones.
    const PIN_CAP0_MODULE_SHA256: &str =
        "6081e7b8e65d35c7b9090a79db7f2af6107a576bc7d9d85c20852c87161ad02c";
    const PIN_CAP0_RUNNABLE_MODULE_SHA256: &str =
        "2adc22d45af440f58119fd601c1779d746b2a4a4966fe7a3a6e98031bbbe1eb9";
    const PIN_WITH_DRIVER_MODULE_SHA256: &str =
        "b499f4b98858401e73e61667198f6611b7b70837f21406e5dbed67586dc4e4cc";

    let checks: [(&str, String, &str); 6] = [
        (
            "cap0 source",
            sha256_hex(cap.as_bytes()),
            PIN_CAP0_SRC_SHA256,
        ),
        (
            "cap0_runnable source",
            sha256_hex(capr.as_bytes()),
            PIN_CAP0_RUNNABLE_SRC_SHA256,
        ),
        (
            "with_driver source",
            sha256_hex(wd.as_bytes()),
            PIN_WITH_DRIVER_SRC_SHA256,
        ),
        (
            "cap0 module",
            sha256_hex(oracle_module_hex("pin7_cap0", &cap).as_bytes()),
            PIN_CAP0_MODULE_SHA256,
        ),
        (
            "cap0_runnable module",
            sha256_hex(oracle_module_hex("pin7_capr", &capr).as_bytes()),
            PIN_CAP0_RUNNABLE_MODULE_SHA256,
        ),
        (
            "with_driver module",
            sha256_hex(oracle_module_hex("pin7_wd", &wd).as_bytes()),
            PIN_WITH_DRIVER_MODULE_SHA256,
        ),
    ];

    let drift: Vec<String> = checks
        .iter()
        .filter(|(_, actual, expected)| actual != expected)
        .map(|(label, actual, expected)| format!("{label}: actual {actual}, pinned {expected}"))
        .collect();
    assert!(
        drift.is_empty(),
        "PIN-7: certified artifact content changed:\n{}\nIf this is intended, update every \
         digest in the same PR with the reason in the commit message (SC-P2).",
        drift.join("\n")
    );
}

/// Pin the number of functions excluded from the certified surface.
#[test]
fn pin_strip_list_length() {
    const PIN_STRIP_LIST_ENTRIES: usize = 6;
    let total = CAP0_STRIP_STRING.len() + CAP0_STRIP_STRINGS.len();
    assert_eq!(
        total, PIN_STRIP_LIST_ENTRIES,
        "PIN-1: the strip list changed to {total} entries (pinned {PIN_STRIP_LIST_ENTRIES}).          Adding a name SHRINKS the certified surface with both stages moving together — the byte          capstones cannot see it. If the change is intended, say why in the commit message and          update this pin (SC-P2); removing a name is a ratchet win."
    );
    // Anti-vacuity: the names must be non-empty and distinct, or the count means nothing.
    let mut all: Vec<&str> = CAP0_STRIP_STRING
        .iter()
        .chain(CAP0_STRIP_STRINGS.iter())
        .copied()
        .collect();
    assert!(
        all.iter().all(|n| !n.is_empty()),
        "a strip-list entry is empty"
    );
    all.sort_unstable();
    let before = all.len();
    all.dedup();
    assert_eq!(all.len(), before, "the strip list contains duplicate names");
}

// ── HB-2: the CHECKED byte capstone — the gates run IN the certified path ────────────────────
//
// The emit-lane capstones above prove Stage-1 == Stage-2 with NO checker in the executed path
// (HB-2's first clause). These tests retire that clause: the SAME composed Stage-1 tool, with
// its `sh_compile` body — nr → tc → ring → effect → taint → cap → own → ai_encode_wasm, every
// gate short-circuiting — runs over the certified artifact (its own source, gates included) and
// must BOTH accept at every gate AND emit the oracle's exact bytes. The mutant suite below is
// the SC-P4 witness that OK is a verdict, not sleep: a corrupted artifact must REJECT at the
// corrupted stage, through this same entry point.

/// Run the composed selfhost compiler WITH gates (`sh_mono_wasm`) at certified-artifact scale.
/// `sh_mono_out` keeps the default 16 MB sandbox for the MONO-4 small-program corpus; cap0-scale
/// input needs the SELF-4 budgets (measured: 92 M fuel for gates + emit — the 10 G budget is the
/// same ceiling the emit-lane capstones use; 256 MB linear memory).
fn sh_mono_out_cap0(src: &str) -> String {
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        sh_mono_wasm(),
        src.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the composed gate compiler executes at cap0 scale");
    String::from_utf8_lossy(&result.output).into_owned()
}

/// HB-2 CHECKED CAPSTONE: the certified artifact passes its OWN full gate chain, and the module
/// emitted BEHIND those gates is byte-identical to the oracle's. "SIGIL checks SIGIL" over the
/// monomorphic fragment — Rust remains bootstrap and oracle (HB-2's surviving clauses).
#[test]
fn hb2_checked_byte_capstone() {
    let input = cap0_input();
    let oracle = oracle_compile("hb2_checked", &input);
    let (okind, _, ohex) = split_protocol(&oracle);
    assert_eq!(
        okind, "OK",
        "Stage-2 (oracle) accepts the certified artifact"
    );

    let out = sh_mono_out_cap0(&input);
    let (kind, stage, shex) = split_protocol(&out);
    assert_eq!(
        (kind.as_str(), stage.as_str()),
        ("OK", ""),
        "every selfhost gate must accept the certified artifact (first reject: {stage} {})",
        shex.chars().take(200).collect::<String>()
    );
    assert!(!shex.contains("!!"), "the checked emit must be poison-free");
    assert_eq!(
        shex.len(),
        ohex.len(),
        "checked Stage-1 and Stage-2 module sizes match"
    );
    assert_eq!(
        shex, ohex,
        "HB-2: the gate-checked selfhost emit is byte-identical to the oracle"
    );
}

/// HB-2 MUTANT SUITE (SC-P4): the checked capstone's OK is a VERDICT, not sleep. Each row
/// injects a minimal violation into the certified artifact and asserts the pipeline rejects at
/// EXACTLY that gate with EXACTLY that headline code, through the same entry point the capstone
/// uses. Every (shape, stage, code) triple below is MEASURED, not predicted — the first candidate
/// set was written from the RUST checkers' mental model and 4 of 7 sailed through the shadows'
/// narrower covered projections (a canary written from the wrong mental model; the tc case then
/// exposed the multi-module vacuity this branch fixes).
///
/// STAGES WITHOUT A ROW — an explicit census, not a silent cap (both are witnessed at the
/// composed-pipeline level by `boot1_every_gate_fires`):
///   * ring — R-codes are module-attr-gated (`#[ring(...)]`); the certified artifact's modules
///     carry no ring attr, and a fn/decl APPEND cannot introduce one.
///   * effect — the SH-EFFECT registration filter is likewise ring-attr-gated: an
///     `effect X; … ! {}` leak appended to the unringed artifact registers nothing (measured OK).
#[test]
fn hb2_checked_capstone_mutants_reject() {
    let base = cap0_input();
    let mutants: &[(&str, &str, &str, &str)] = &[
        ("nr: unresolved use", "\nuse hb2_missing;\n", "nr", "N007"),
        (
            "tc: let bool = int-literal",
            "\nfn hb2_mut_tc() -> i64 { let x: bool = 5; return 0; }\n",
            "tc",
            "T041",
        ),
        (
            "taint: @Secret to public return",
            "\nfn hb2_mut_tt(s: i64 @Secret) -> i64 { return s; }\n",
            "taint",
            "T001",
        ),
        (
            "cap: attenuated sink",
            "\ncap type Hb2Fuel { burn, query }\nfn hb2_need(f: Hb2Fuel) -> i64 { return 1; }\nfn hb2_go(f: Hb2Fuel) -> i64 { let r: Hb2Fuel = f.restrict(burn); return hb2_need(r); }\n",
            "cap",
            "C003",
        ),
        (
            "own: double consume",
            "\ncap type Hb2Own {}\nfn hb2_need2(f: Hb2Own) -> i64 { return 1; }\nfn hb2_own(f: Hb2Own) -> i64 { let a: i64 = hb2_need2(f); let b: i64 = hb2_need2(f); return a; }\n",
            "own",
            "O001",
        ),
    ];
    for (label, snippet, want_stage, want_code) in mutants {
        let mutated = format!("{base}{snippet}");
        let out = sh_mono_out_cap0(&mutated);
        let (kind, stage, detail) = split_protocol(&out);
        assert_eq!(
            (kind.as_str(), stage.as_str()),
            ("REJECT", *want_stage),
            "mutant `{label}` must reject at {want_stage}: got {kind}:{stage} {}",
            detail.chars().take(120).collect::<String>()
        );
        assert!(
            detail
                .split(';')
                .any(|c| c.split(',').next() == Some(*want_code)),
            "mutant `{label}` must carry {want_code}: {detail}"
        );
    }
}

/// HB-2: a genuinely-UNDEFINED callee now rejects AT TC — the pin this test previously held
/// ("passes every gate, fails closed at the emit's `!!` poison") flipped DELIBERATELY when the
/// shadow gained intrinsic sigs + bare-variant resolution and T062 returned to gate 2's
/// enforced set, exactly as this test's earlier comment said it would. The emit poison remains
/// the last-line backstop for anything still outside the covered projection.
#[test]
fn hb2_unknown_callee_rejects_at_tc() {
    let base = cap0_input();
    let mutated = format!("{base}\nfn hb2_mut_nr() -> i64 {{ return hb2_no_such_fn(); }}\n");
    let out = sh_mono_out_cap0(&mutated);
    let (kind, stage, detail) = split_protocol(&out);
    assert_eq!(
        (kind.as_str(), stage.as_str()),
        ("REJECT", "tc"),
        "an undefined callee must reject at the tc gate: {detail}"
    );
    assert!(
        detail
            .split(';')
            .any(|c| c.split(',').next() == Some("T062")),
        "the rejection must carry T062: {detail}"
    );
}

// ── HB-1: the STUB-FREE executable fixed point, gates IN the executed body ───────────────────
//
// Claim 5's executable round trip used a minimal splice stub; #684 retired the never-EXECUTED
// caveat with an emit-lane driver; and this section retires HB-1's LAST residue: `tool_main` now
// drives the full `sh_compile` chain, so the seven gates run inside the artifact's own executed
// body. The fixed point is now protocol-shaped — F(source(F)) = `OK:` + hex(F) — and the
// BOOT_CORPUS differential below witnesses every gate firing IN the executed module.

/// The oracle-compiled with-driver module + its certified hex, built once and shared by the
/// executed-artifact tests (each execution is cheap next to the 1.15 MB oracle compile).
fn with_driver_artifact() -> &'static (Vec<u8>, String) {
    static A: std::sync::OnceLock<(Vec<u8>, String)> = std::sync::OnceLock::new();
    A.get_or_init(|| {
        let input = with_driver_input();
        let (okind, _, ohex) = split_protocol(&oracle_compile("hb1_artifact", &input));
        assert_eq!(okind, "OK", "the oracle accepts the with-driver artifact");
        (unhex(&ohex), ohex)
    })
}

/// Execute the with-driver artifact on `src` under the standard SELF-4 budgets.
fn run_artifact(src: &str) -> String {
    let art = with_driver_artifact();
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        &art.0,
        src.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the with-driver artifact executes");
    // Strict, matching `sh_mono_out`: lossy decoding would silently map non-UTF-8 output to
    // U+FFFD and let a corrupt run be compared as if it were text.
    String::from_utf8(result.output).expect("the artifact's output is UTF-8")
}

/// The with-driver artifact, EXECUTED on its own source, gates it and emits its own bytes:
/// F(source(F)) = `OK:` + hex(F). The oracle compiles the certified source once (Stage-1 emits
/// the identical module — `ag6_5_with_driver_byte_capstone`); executing THAT module on the same
/// source must pass all seven of ITS OWN gates and reproduce the same hex. The emit-lane form
/// measured 74 M fuel on 2026-08-01; the gated form adds the gate walk under the same 10 G
/// SELF-4 ceiling.
#[test]
fn hb1_stub_free_executable_fixed_point() {
    let input = with_driver_input();
    let art = with_driver_artifact();
    let out = run_artifact(&input);
    let (kind, stage, hex) = split_protocol(&out);
    assert_eq!(
        (kind.as_str(), stage.as_str()),
        ("OK", ""),
        "the executed artifact's own gate chain must accept its own source (first reject: {})",
        hex.chars().take(200).collect::<String>()
    );
    assert!(!hex.contains("!!"), "the self-compile must be poison-free");
    assert_eq!(
        hex.len(),
        art.1.len(),
        "the self-compiled module's size must equal the artifact's own"
    );
    assert_eq!(
        hex, art.1,
        "HB-1: the executed artifact gates its own source and reproduces its own bytes"
    );
}

/// SC-P4 witness for claims 36/38: the `OK` those tests assert is a VERDICT reached through the
/// EXECUTED artifact's own gates, not merely a chain that reached emit.
///
/// The mutant suite for the checked capstone (`hb2_checked_capstone_mutants_reject`) runs its
/// mutants through `sh_mono_out_cap0` — the test-side `sh_mono_wasm` binary. That leaves the
/// executed artifact's own `OK` unwitnessed: a gate vacuous ONLY in the oracle's compilation of
/// the certified source (precisely the trusting-trust case this section exists for) would be
/// invisible. One mutant per injectable gate, fed through `run_artifact`, closes that.
#[test]
fn hb1_executed_artifact_rejects_mutants() {
    let base = with_driver_input();
    let mutants: &[(&str, &str, &str, &str)] = &[
        ("nr: unresolved use", "\nuse hb1_missing;\n", "nr", "N007"),
        (
            "tc: let bool = int-literal",
            "\nfn hb1_mut_tc() -> i64 { let x: bool = 5; return 0; }\n",
            "tc",
            "T041",
        ),
        (
            "taint: @Secret to public return",
            "\nfn hb1_mut_tt(s: i64 @Secret) -> i64 { return s; }\n",
            "taint",
            "T001",
        ),
        (
            "cap: attenuated sink",
            "\ncap type Hb1Fuel { burn, query }\nfn hb1_need(f: Hb1Fuel) -> i64 { return 1; }\nfn hb1_go(f: Hb1Fuel) -> i64 { let r: Hb1Fuel = f.restrict(burn); return hb1_need(r); }\n",
            "cap",
            "C003",
        ),
        (
            "own: double consume",
            "\ncap type Hb1Own {}\nfn hb1_need2(f: Hb1Own) -> i64 { return 1; }\nfn hb1_own(f: Hb1Own) -> i64 { let a: i64 = hb1_need2(f); let b: i64 = hb1_need2(f); return a; }\n",
            "own",
            "O001",
        ),
    ];
    for (label, snippet, want_stage, want_code) in mutants {
        let out = run_artifact(&format!("{base}{snippet}"));
        let (kind, stage, detail) = split_protocol(&out);
        assert_eq!(
            (kind.as_str(), stage.as_str()),
            ("REJECT", *want_stage),
            "mutant `{label}` must reject at {want_stage} through the EXECUTED artifact: got \
             {kind}:{stage} {}",
            detail.chars().take(120).collect::<String>()
        );
        assert!(
            detail
                .split(';')
                .any(|c| c.split(',').next() == Some(*want_code)),
            "mutant `{label}` must carry {want_code}: {detail}"
        );
    }
}

/// SC-P4 witness: the fixed point is a VERDICT about self-reproduction, not an echo chamber.
/// The same executed artifact is a working COMPILER on other inputs — fed a different covered
/// program it emits exactly what the oracle emits for THAT program (and thus NOT its own bytes).
#[test]
fn hb1_executed_artifact_is_a_compiler_not_an_echo() {
    let art = with_driver_artifact();

    // A different covered program: the boot corpus's while-loop accept.
    let other = "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let mut s: i64 = 0; let mut i: i64 = 0; while i < 10 { s = s + i; i = i + 1; } return 0 - s; }\n";
    let oracle_other = oracle_compile("hb1_echo_other", other);
    let (okind2, _, other_hex) = split_protocol(&oracle_other);
    assert_eq!(okind2, "OK", "the oracle accepts the other program");
    let out = run_artifact(other);
    let (kind, _, hex) = split_protocol(&out);
    assert_eq!(
        kind, "OK",
        "the executed artifact accepts the other program"
    );
    assert_eq!(
        hex, other_hex,
        "the executed artifact must agree with the oracle on OTHER inputs"
    );
    assert_ne!(
        hex, art.1,
        "…and must NOT echo its own bytes for a different input"
    );
}

/// SC-P4 witness that the GATES live in the EXECUTED body: the executed artifact, fed the whole
/// BOOT_CORPUS, must agree with the composed test-side pipeline EXACTLY — accepts as `OK:<hex>`,
/// rejects at the same gate with the same detail string. The corpus carries a reject for every
/// gate (including ring and effect, which the append-mutant suite structurally cannot fire on
/// the unringed artifact), so a driver that routed around any gate would accept that gate's
/// reject row and fail here; the closing coverage assertion makes that completeness explicit.
#[test]
fn hb1_executed_artifact_runs_the_gates() {
    let mut reject_stages = std::collections::BTreeSet::new();
    for (label, src, want) in BOOT_CORPUS {
        let exec = run_artifact(src);
        let composed = sh_mono_out(src);
        assert_eq!(
            exec, composed,
            "BOOT_CORPUS `{label}`: the executed artifact must match the composed pipeline"
        );
        let (kind, stage, detail) = split_protocol(&exec);
        if *want == "OK" {
            assert_eq!(kind, "OK", "`{label}` expected accept");
            // An accept is only meaningful if it CARRIES A MODULE. `sh_compile` returns
            // `OK:` + `ai_encode_wasm(...)`, and that emitter returns the whole-output poison
            // sentinel `"!!"` when any function poisoned (selfhost/air.sigil:7203) — so `OK:!!`
            // and `OK:` are both reachable outputs that a kind-only check accepts as a compile.
            // Both sides of the equality above would carry the same sentinel, so the differential
            // cannot see it either. Pin the accept against the ORACLE's bytes for this program:
            // now an accept means the artifact emitted the right module, not merely that it
            // reached emit.
            assert!(
                !detail.is_empty() && !detail.contains("!!"),
                "`{label}`: accept must carry a real module, not the `!!` poison sentinel or an \
                 empty payload"
            );
            let (okind, _, ohex) = split_protocol(&oracle_compile(label, src));
            assert_eq!(okind, "OK", "`{label}`: the oracle must accept this row");
            assert_eq!(
                detail, ohex,
                "`{label}`: the executed artifact's accept must be the oracle's exact module"
            );
        } else {
            assert_eq!(
                (kind.as_str(), stage.as_str()),
                ("REJECT", *want),
                "`{label}` expected reject at {want}"
            );
            // Stage name alone is not a verdict: `REJECT:{stage}:` with an EMPTY code list
            // matches, and for taint so does `SH_TAINT_UNSUPPORTED` — which is inside that gate's
            // allowlist (selfhost/pipeline.sigil:197). A shadow whose covered projection narrowed
            // until the row hit the fail-closed path instead of its real code would still look
            // green here while the actual detection was dead.
            assert!(
                !detail.is_empty(),
                "`{label}`: a reject must carry at least one code"
            );
            assert!(
                !detail.contains("SH_TAINT_UNSUPPORTED"),
                "`{label}`: rejected via the fail-closed unsupported path, not its real code — \
                 the covered projection narrowed: {detail}"
            );
            reject_stages.insert(stage);
        }
    }
    // The witness is only as strong as its coverage: every gate must have fired.
    let stages: Vec<String> = reject_stages.into_iter().collect();
    let want: Vec<String> = ["cap", "effect", "nr", "own", "ring", "taint", "tc"]
        .iter()
        .map(|s| s.to_string())
        .collect();
    assert_eq!(
        stages, want,
        "the executed-gates witness must cover every gate"
    );
}

/// MULTI-MODULE reject rows — the fence for the bug class that produced the vacuous tc gate.
///
/// That defect (#682) was a gate whose walk expected functions at the root and therefore returned
/// EMPTY over a multi-module program; the pipeline read empty diags as PASS. The certified
/// artifact is multi-module (`module tool;` … `module string;` … `module strings;` …
/// `module option;`), so the vacuity was live on exactly the input that matters — yet of the
/// seventeen `BOOT_CORPUS` rows only two are multi-module, and both target `nr`. The corpus's
/// shape coverage pointed away from the known failure mode.
///
/// Each row below places its violation in the SECOND module, so a gate that only ever walks the
/// first (or the root) returns clean and the row goes red.
#[test]
fn hb1_multi_module_rejects_fence_the_vacuous_gate_class() {
    const MULTI: &[(&str, &str, &str, &str)] = &[
        (
            "mm_tc_second_module",
            "module one;\nfn a() -> i64 { return 1; }\nmodule two;\nfn b() -> i64 { let x: bool = 5; return 0; }\n",
            "tc",
            "T041",
        ),
        (
            "mm_taint_second_module",
            "module one;\nfn a() -> i64 { return 1; }\nmodule two;\nfn leak(s: i64 @Secret) -> i64 { return s; }\n",
            "taint",
            "T001",
        ),
        (
            "mm_cap_second_module",
            "module one;\nfn a() -> i64 { return 1; }\nmodule sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return need(r); }\n",
            "cap",
            "C003",
        ),
        (
            "mm_own_second_module",
            "module one;\nfn a() -> i64 { return 1; }\nmodule sigil;\ncap type Fuel {}\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let x: i64 = need(f); let y: i64 = need(f); return x; }\n",
            "own",
            "O001",
        ),
    ];
    for (label, src, want_stage, want_code) in MULTI {
        let exec = run_artifact(src);
        assert_eq!(
            exec,
            sh_mono_out(src),
            "`{label}`: executed artifact must match the composed pipeline"
        );
        let (kind, stage, detail) = split_protocol(&exec);
        assert_eq!(
            (kind.as_str(), stage.as_str()),
            ("REJECT", *want_stage),
            "`{label}`: a violation in the SECOND module must still reject at {want_stage} — a \
             gate that walks only the first module returns clean here: got {kind}:{stage} {}",
            detail.chars().take(160).collect::<String>()
        );
        assert!(
            detail
                .split(';')
                .any(|c| c.split(',').next() == Some(*want_code)),
            "`{label}`: must carry {want_code}: {detail}"
        );
    }
}

// ── SEED: the committed compiler binary + succession (HB-1's lineage bound) ──────────────────
//
// The fixed point (claims 36–37) executes an artifact the ORACLE compiles at test time — proof
// that the artifact reproduces itself, not that the repo carries a lineage of artifacts. These
// tests freeze the artifact as a committed, digest-pinned seed and make its self-regeneration a
// CI property. Succession is a RITUAL with a DDC-shaped agreement check (`seed_regenerate`):
// when the certified source moves, the NEXT seed is written from the OLD seed's own output,
// asserted byte-equal to the oracle's emit first — a divergence is a trusting-trust alarm,
// never an overwrite. Provenance (which run produced which seed) lives in seed/PROVENANCE.md;
// the genesis seed is necessarily oracle-built, HB-1's permanent caveat.

/// SHA-256 of the committed seed's RAW bytes (distinct from PIN_WITH_DRIVER_MODULE_SHA256,
/// which digests the oracle's HEX STRING).
const PIN_SEED_SHA256: &str = "4062f4e19707f9dcaa51c71bb11f9cec73ddbfa2d12c8e38f127c8a3e705ac39";

/// Environment variable that ARMS the succession ritual's write. Without it the ritual VERIFIES
/// instead of writing (see `seed_regenerate`).
const SEED_REGENERATE_ENV: &str = "SIGIL_SEED_REGENERATE";

/// Absolute path to the committed seed, derived from the crate's compile-time manifest directory
/// rather than the process CWD. A bare `../../seed/...` is correct under `cargo test` and
/// `nextest` (both set CWD to the package root) but resolves somewhere else entirely when the
/// test binary is run directly from `target/debug/deps` — and combined with a create-then-write
/// it would put an artifact OUTSIDE the repository while reporting success. Every other
/// repo-root reference in this file is `include_str!` (compile-time); this is the same property
/// for a runtime path.
fn seed_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("sigil-runtime must live under crates/")
        .join("seed")
        .join("sigil-seed.wasm")
}

fn read_seed() -> Vec<u8> {
    let path = seed_path();
    match std::fs::read(&path) {
        Ok(bytes) => bytes,
        Err(e) => panic!(
            "PIN-SEED: cannot read the committed seed at {}: {e}\n\
             Most likely the checkout is incomplete (a sparse or filtered clone omits `seed/`) \
             or the file is locked/unreadable — fix the checkout first: `git checkout -- seed/`.\n\
             ONLY if the certified source genuinely moved, run the succession ritual in the SAME \
             PR: {SEED_REGENERATE_ENV}=1 cargo test -p sigil-runtime --test pipeline_differential \
             seed_regenerate -- --ignored --nocapture, then repin PIN_SEED_SHA256 and append a \
             row to seed/PROVENANCE.md.",
            path.display()
        ),
    }
}

/// Compare byte vectors with a READABLE failure. `assert_eq!` on two 464 KB `Vec<u8>` renders
/// both sides with `{:?}` — about 4.6 MB of log with no indication of where they diverge, on
/// exactly the failure path these pins exist to catch. Report sizes, digests, and the first
/// differing offset instead, matching the `drift` idiom the PIN-1/PIN-7 tests already use.
fn assert_bytes_eq(actual: &[u8], expected: &[u8], what: &str) {
    if actual == expected {
        return;
    }
    let where_ = match actual.iter().zip(expected).position(|(a, b)| a != b) {
        Some(i) => format!(
            "first differing offset {i} (actual {:#04x}, expected {:#04x})",
            actual[i], expected[i]
        ),
        None => "no differing byte — one is a prefix of the other".to_string(),
    };
    panic!(
        "{what}\n  actual:   {} B, sha256 {}\n  expected: {} B, sha256 {}\n  {where_}",
        actual.len(),
        sha256_hex(actual),
        expected.len(),
        sha256_hex(expected),
    );
}

/// SEED pin: the committed binary IS the oracle's emit of the certified source, byte-identical,
/// at the pinned size and digest. A moved certified source without a same-PR succession fails
/// here — the seed cannot silently go stale.
#[test]
fn seed_is_the_oracle_emit_of_the_certified_source() {
    let seed = read_seed();
    let art = with_driver_artifact();
    assert_eq!(
        seed.len(),
        PIN_WITH_DRIVER_MODULE_BYTES,
        "the seed's size is the certified module size"
    );
    assert_eq!(
        sha256_hex(&seed),
        PIN_SEED_SHA256,
        "the seed's raw-bytes digest is pinned (SC-P1: repin the measured value with the reason)"
    );
    assert_bytes_eq(
        &seed,
        &art.0,
        "PIN-SEED: the committed seed is NOT the oracle's emit of the certified source. If the \
         certified source moved, run the succession ritual in this same PR (see seed_regenerate).",
    );
    // SC-P4 anti-stub: the digest comparator must distinguish content — a single flipped byte
    // must change the digest, or the pin above pins nothing.
    let mut flipped = seed.clone();
    let mid = flipped.len() / 2;
    flipped[mid] ^= 0x01;
    assert_ne!(
        sha256_hex(&flipped),
        PIN_SEED_SHA256,
        "anti-stub: a flipped byte must break the digest"
    );
}

/// SEED self-regeneration: EXECUTING the committed seed on the certified source reproduces the
/// seed byte-exactly — the fixed point (claim 36) holds of the committed binary itself, not just
/// of a module the oracle compiled moments earlier. The run passes through the seed's own seven
/// gates (the seed IS the gated artifact).
#[test]
fn seed_self_regenerates() {
    let seed = read_seed();
    let input = with_driver_input();
    let result = sigil_runtime::execute_ephemeral_with_memory_budget(
        &seed,
        input.as_bytes(),
        10_000_000_000,
        256 * 1024 * 1024,
        &sigil_runtime::grants::IoGrants::none(),
    )
    .expect("the committed seed executes on the certified source");
    let out = String::from_utf8_lossy(&result.output).into_owned();
    let (kind, stage, hex) = split_protocol(&out);
    assert_eq!(
        (kind.as_str(), stage.as_str()),
        ("OK", ""),
        "the committed seed's gate chain must accept the certified source (rejected at {stage} \
         with: {})",
        hex.chars().take(200).collect::<String>()
    );
    assert!(
        !hex.contains("!!"),
        "the seed's self-emit must be poison-free, not the `!!` sentinel"
    );
    assert_bytes_eq(
        &unhex(&hex),
        &seed,
        "run(seed, source(seed)) must reproduce the seed byte-exactly",
    );
}

/// THE SUCCESSION RITUAL (run explicitly when the certified source moves; ignored in CI):
///
///   SIGIL_SEED_REGENERATE=1 cargo test -p sigil-runtime --test pipeline_differential \
///       seed_regenerate -- --ignored --nocapture
///
/// Succession: the OLD committed seed compiles the NEW certified source, its output is asserted
/// byte-equal to the oracle's emit (the DDC agreement check — a divergence is a trusting-trust
/// alarm and must NOT be committed), and only that agreed output is written as the next seed.
/// The written bytes are the OLD SEED'S OUTPUT, so lineage stays seed-built after genesis.
/// Genesis (no committed seed) falls back to the oracle's emit — record it as such in
/// seed/PROVENANCE.md.
///
/// THREE GUARDS, each closing a measured way this could destroy the artifact it exists to
/// maintain:
///   * ARMED BY ENV VAR. `#[ignore]` alone is not a guard: `cargo test -- --include-ignored` is a
///     plausible "run everything" invocation, and libtest runs tests as threads in one process,
///     so an unguarded truncate-then-write races `read_seed` in the two tests above. Without
///     `SIGIL_SEED_REGENERATE=1` this test VERIFIES (recomputing succession and asserting it
///     reproduces the committed bytes) and writes nothing.
///   * GENESIS ONLY ON NotFound. A blanket `Err(_)` treats a locked or unreadable file — routine
///     on Windows — as "no seed yet", silently SKIPPING the DDC agreement check and writing an
///     oracle-built artifact that a later PROVENANCE row would misrecord as a succession. Nothing
///     in the bytes can distinguish the two afterwards, so this arm must be exact.
///   * ATOMIC WRITE + READ-BACK. `fs::write` truncates first, so a full disk (a recurring
///     condition on this machine) destroys the committed seed and leaves a partial file that the
///     NEXT run reads as a corrupt "old seed" — reporting a trusting-trust alarm for a disk
///     problem. Write a sibling temp file, verify its bytes, then rename over.
#[test]
#[ignore = "succession ritual — set SIGIL_SEED_REGENERATE=1 to write; run with --ignored --nocapture"]
fn seed_regenerate() {
    let input = with_driver_input();
    let art = with_driver_artifact();
    let path = seed_path();
    let armed = std::env::var(SEED_REGENERATE_ENV).is_ok_and(|v| v == "1");

    let new_bytes = match std::fs::read(&path) {
        Ok(old_seed) => {
            let result = sigil_runtime::execute_ephemeral_with_memory_budget(
                &old_seed,
                input.as_bytes(),
                10_000_000_000,
                256 * 1024 * 1024,
                &sigil_runtime::grants::IoGrants::none(),
            )
            .expect("succession: the old seed executes on the current certified source");
            let out = String::from_utf8_lossy(&result.output).into_owned();
            let (kind, stage, hex) = split_protocol(&out);
            assert_eq!(
                (kind.as_str(), stage.as_str()),
                ("OK", ""),
                "succession: the old seed must accept the current certified source (rejected at \
                 {stage} with: {})",
                hex.chars().take(200).collect::<String>()
            );
            let bytes = unhex(&hex);
            if bytes == art.0 {
                println!("SUCCESSION: next seed = the old seed's output (oracle-agreed)");
                bytes
            } else {
                // EMITTER-RULE SUCCESSION (two stages). When the certified source changes what
                // the compiler EMITS — not only what it accepts — the old seed applies its own
                // emission rules to the new source and cannot agree with the oracle at stage
                // one, although the compiler it just built implements the new rules. The
                // classic diverse-double-compilation answer is one more stage: the compiler the
                // old seed built (M1, lineage-carrying) compiles the certified source again, and
                // THAT output must agree with the oracle byte-exactly and be its own fixed
                // point. Lineage is preserved (the new seed was built by a compiler the old seed
                // built); a disagreement at stage two is the genuine trusting-trust alarm. The
                // provenance row must name the emission change that made the second stage
                // necessary.
                let stage_one = bytes;
                let second = sigil_runtime::execute_ephemeral_with_memory_budget(
                    &stage_one,
                    input.as_bytes(),
                    10_000_000_000,
                    256 * 1024 * 1024,
                    &sigil_runtime::grants::IoGrants::none(),
                )
                .expect("emitter-rule succession: the stage-one compiler executes on the certified source");
                let out = String::from_utf8_lossy(&second.output).into_owned();
                let (kind, stage, hex) = split_protocol(&out);
                assert_eq!(
                    (kind.as_str(), stage.as_str()),
                    ("OK", ""),
                    "emitter-rule succession: the stage-one compiler must accept the certified \
                     source (rejected at {stage} with: {})",
                    hex.chars().take(200).collect::<String>()
                );
                let stage_two = unhex(&hex);
                assert_bytes_eq(
                    &stage_two,
                    &art.0,
                    "DDC succession: neither run(old_seed, new_source) nor \
                     run(run(old_seed, new_source), new_source) agrees with oracle(new_source) \
                     byte-exactly. DIVERGENCE IS A TRUSTING-TRUST ALARM — do not overwrite the \
                     seed; find which compiler changed meaning.",
                );
                println!(
                    "SUCCESSION (emitter-rule, two stages): stage one differed from the oracle by \
                     {} bytes; next seed = the stage-one compiler's output (oracle-agreed)",
                    stage_one.len().abs_diff(art.0.len())
                );
                stage_two
            }
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            println!(
                "GENESIS: no committed seed at {}; seeding from the oracle's emit — record as \
                 oracle-built in seed/PROVENANCE.md",
                path.display()
            );
            art.0.clone()
        }
        Err(e) => panic!(
            "succession: the committed seed at {} exists but could not be read: {e}. This is NOT \
             a genesis — refusing to skip the lineage check. Fix the file (`git checkout -- \
             seed/`), then re-run.",
            path.display()
        ),
    };

    if !armed {
        assert_bytes_eq(
            &new_bytes,
            &read_seed(),
            "succession VERIFY (unarmed): the recomputed seed differs from the committed one. \
             Set SIGIL_SEED_REGENERATE=1 to write it, and record the reason in \
             seed/PROVENANCE.md.",
        );
        println!(
            "VERIFY-ONLY: succession reproduces the committed seed; nothing written. Set \
             {SEED_REGENERATE_ENV}=1 to write."
        );
        return;
    }

    std::fs::create_dir_all(path.parent().expect("seed path has a parent"))
        .expect("seed dir exists");
    let tmp = path.with_extension("wasm.new");
    std::fs::write(&tmp, &new_bytes).expect("seed temp written");
    let readback = std::fs::read(&tmp).expect("seed temp readable");
    assert_bytes_eq(
        &readback,
        &new_bytes,
        "succession: the temp file did not read back byte-identically (disk full or truncated) — \
         the committed seed is UNTOUCHED",
    );
    std::fs::rename(&tmp, &path).expect("seed temp renamed over the committed seed");
    println!(
        "seed/sigil-seed.wasm written: {} bytes, sha256 {}",
        new_bytes.len(),
        sha256_hex(&new_bytes)
    );
}

/// `seed/PROVENANCE.md` is the ONE record the CI lane cannot carry — which run produced which
/// seed. It was also the one record nothing checked: a succession that repins `PIN_SEED_SHA256`
/// but forgets the row (or transposes a digit) leaves every other test green while the sole
/// lineage record points at bytes that are not in the repo. This reads the newest table row and
/// requires it to describe the committed artifact.
#[test]
fn seed_provenance_row_matches_the_committed_seed() {
    let path = seed_path().with_file_name("PROVENANCE.md");
    let doc = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("seed/PROVENANCE.md is committed ({}): {e}", path.display()));

    // Table rows only: a leading `|`, and not the header or its `---` separator.
    let rows: Vec<Vec<String>> = doc
        .lines()
        .map(str::trim)
        .filter(|l| l.starts_with('|') && !l.contains("---") && !l.contains("date (UTC)"))
        .map(|l| {
            l.trim_matches('|')
                .split('|')
                .map(|c| c.trim().trim_matches('`').to_string())
                .collect()
        })
        .collect();
    assert!(
        !rows.is_empty(),
        "PROVENANCE: no data rows found — the lineage record is empty or its table shape changed"
    );
    let last = rows.last().expect("a row exists");
    assert!(
        last.len() >= 5,
        "PROVENANCE: the newest row has {} columns, expected at least 5 \
         (date | event | source sha | seed sha | bytes | produced by): {last:?}",
        last.len()
    );

    let seed = read_seed();
    assert_eq!(
        last[3],
        sha256_hex(&seed),
        "PROVENANCE: the newest row's seed digest does not match the committed seed. Append (or \
         correct) the row for the succession that produced these bytes."
    );
    assert_eq!(
        last[2],
        sha256_hex(with_driver_input().as_bytes()),
        "PROVENANCE: the newest row's SOURCE digest does not match the current certified source"
    );
    assert_eq!(
        last[4].replace(',', "").parse::<usize>().ok(),
        Some(seed.len()),
        "PROVENANCE: the newest row's byte count does not match the committed seed"
    );

    // SC-P4 anti-stub: the row parser must actually read distinct fields, not return blanks that
    // compare equal to whatever they are checked against.
    assert!(
        last.iter().take(5).all(|c| !c.is_empty()),
        "anti-stub: a blank cell would make these comparisons meaningless: {last:?}"
    );
    assert_eq!(
        last[3].len(),
        64,
        "anti-stub: the seed-digest cell must be a full sha256"
    );
}

/// Count `StrBytesEq` statements in a lowered AIR program.
fn count_str_bytes_eq(program: &air::AirProgram) -> usize {
    program
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.stmts.iter())
        .filter(|s| matches!(s, air::AirStmt::StrBytesEq { .. }))
        .count()
}

/// Lower a source string to AIR, asserting it is clean through type-check.
fn lower_to_air(label: &str, src: &str) -> air::AirProgram {
    let source = SourceFile::new(label, src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(pdiags.is_empty(), "{label}: fixture must be parse-clean");
    let resolved = name_resolution::resolve(&ast).expect("name resolution");
    let (typed, _) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .unwrap_or_else(|ds| {
            panic!(
                "{label}: type check failed: {:?}",
                ds.iter().map(|d| d.code().to_string()).collect::<Vec<_>>()
            )
        });
    air::lower(&typed)
}

/// SHADOW FENCE. The certified source must contain no `str` content equality.
///
/// `str` `==`/`!=` and string-literal `match` arms all lower to
/// `AirStmt::StrBytesEq`. `selfhost/air.sigil` has NO lowering for it — it
/// emits an unconditional binary op for every `P_K_BINARY` — and it cannot
/// reproduce the `fuel.rs` ceiling-poison that the variant carries, which the
/// self-hosted fuel shadow mirrors bit-exactly. So the day the certified source
/// grows one of these, Stage-1 and Stage-2 diverge in BOTH the AIR shape and
/// the fuel report, silently and at the same moment.
///
/// The divergence is fenced rather than closed because the certified source has
/// no need for it: `.bytes_eq()` computes the identical predicate and is
/// already the idiom there (288 call sites). Teaching the shadow the lowering
/// would mean editing the certified source, which is the expensive direction.
///
/// This scans the LOWERED AIR rather than the text or the untyped AST. A text
/// grep cannot tell `str ==` from `i64 ==`, and an AST walk misses comparisons
/// between two `str` variables. One predicate covers `==`, `!=`, and
/// `match "lit"` because all three funnel into the single variant.
#[test]
fn certified_source_contains_no_str_content_equality() {
    // Anti-stub (SC-P4): an assertion of ABSENCE is only evidence if the
    // instrument can see the thing when it IS present. Prove that first.
    let probe = lower_to_air(
        "str_eq_probe",
        "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
         let a: str = \"x\";
         let b: str = \"y\";
         let e: bool = a == b;
         if e { return 0 - 1; } else { return 0 - 2; }
}
",
    );
    assert_eq!(
        count_str_bytes_eq(&probe),
        1,
        "anti-stub: the scanner must see a real `str ==` before its zero-count          assertion below means anything"
    );

    for (label, src) in [
        ("cap0", cap0_input()),
        ("cap0_runnable", cap0_input_runnable()),
        ("with_driver", with_driver_input()),
    ] {
        let air_program = lower_to_air(label, &src);
        assert_eq!(
            count_str_bytes_eq(&air_program),
            0,
            "SHADOW GAP in `{label}`: the certified source now contains a `str` `==`/`!=` or a              string-literal `match` arm. `selfhost/air.sigil` has no lowering for it and the fuel              shadow cannot reproduce its ceiling-poison, so Stage-1 and Stage-2 would diverge              silently. Use `.bytes_eq()` — the identical predicate and the established idiom              there — or teach `selfhost/air.sigil` the lowering and run the full repin ritual."
        );
    }
}
