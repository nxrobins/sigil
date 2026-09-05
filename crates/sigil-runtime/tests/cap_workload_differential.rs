//! SH-CAP — differential parity for the self-hosted capability-obligation shadow.
//!
//! The oracle is the Pure collector (`air_capability_v2::collector`, Z3-free, quarantined):
//! one obligation per cap-typed arg at each Call / Spawn / Serialize sink plus cap-typed
//! Returns, carrying `required_mask` (= `full_mask` of the ARG's own cap type — the sink
//! demands full authority, callee-blind) and `actual_mask` (`trace_static_authority`, the
//! flow-INsensitive whole-fn last-def-wins static trace). This lane builds sigil-compiler
//! with `default-features = false` — NO solver — so the entire differential is structurally
//! Z3-free (the epic's honesty line). The bitwise-verdict ⇔ Z3-C003 equivalence proof lives
//! in sigil-compiler's own tests under `cfg(feature = "solver")`, on the solver CI lane.
//!
//! The compared render is FROZEN (X-C7): one line per obligation,
//! `{kind} {cap_type} {required_mask} {actual_mask}`, newline-joined, program order
//! (functions → blocks → stmts; a block's Return obligation after its stmts). `var_id` is
//! EXCLUDED by decision (AG-CAP-VARID): it is the AIR VarId of the sink arg — often a
//! lowering temp — and reproducing temps is the CV var-allocation discipline extended to
//! cap forms, a possible future CV-CAPS slice.

use sigil_compiler::CompileOptions;
use sigil_compiler::air;
use sigil_compiler::air_capability_v2;
use sigil_compiler::air_capability_v2::obligations::AirCapabilityWorkload;
use sigil_compiler::compile_tool;
use sigil_compiler::name_resolution;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use sigil_compiler::type_check;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

const LEXER: &str = include_str!("../../../selfhost/lexer.sigil");
const PARSER: &str = include_str!("../../../selfhost/parser.sigil");
const TYPECHECK: &str = include_str!("../../../selfhost/typecheck.sigil");
const CAPCHECK: &str = include_str!("../../../selfhost/cap_check.sigil");
const CAP_FUEL: u64 = 300_000_000;

/// The frozen X-C7 render: `{kind:?} {cap_type} {required} {actual}` per obligation,
/// program order, newline-joined. Empty workload → "".
fn render_workload(w: &AirCapabilityWorkload) -> String {
    w.obligations
        .iter()
        .map(|o| {
            format!(
                "{:?} {} {} {}",
                o.kind, o.cap_type, o.required_mask, o.actual_mask
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Run the oracle pipeline on a fixture: parse → resolve → type_check (yields the
/// AuthorityRegistry) → air::lower → the Pure collector. Panics (naming the fixture) on
/// any parse/resolve/type error — the corpus contract is parse-clean + type-clean.
fn cap_workload_oracle(label: &str, src: &str) -> AirCapabilityWorkload {
    let source = SourceFile::new("<cap-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(
        pdiags.is_empty(),
        "SH-CAP {label}: fixture must be parse-clean, got {pdiags:?}\n{src}"
    );
    let resolved = name_resolution::resolve(&ast)
        .unwrap_or_else(|e| panic!("SH-CAP {label}: fixture must resolve, got {e:?}\n{src}"));
    let (typed, registry) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .unwrap_or_else(|e| {
            panic!("SH-CAP {label}: fixture must type-check (ET-R7), got {e:?}\n{src}")
        });
    let lowered = air::lower(&typed);
    let (cdiags, workload) =
        air_capability_v2::collect_air_capability_workload_for_test(&lowered, &registry);
    assert!(
        cdiags.is_empty(),
        "SH-CAP {label}: the collector emits no standalone diagnostics today, got {cdiags:?}"
    );
    workload
}

/// The CAP-0 pinned corpus: (label, fixture, expected frozen render). Every fixture is
/// parse-clean + type-clean (the oracle fn asserts it); `module sigil;` keeps cap decls in
/// the privileged package. Corpus discipline (X-C10): cap-op receivers are let-bound names;
/// lets annotated except the one MI-3 inference fixture (`w_unannotated_let`).
///
/// Pin provenance (Phase-0 probe, 2026-07-07):
/// - the four sink kinds each pin one obligation of their kind (Call/Return/Serialize/Spawn);
/// - `split` PRESERVES authority (spawn_clean pins `3 3` — trace_static_authority follows
///   src through CapSplit unchanged);
/// - the X-C8 degenerate accepts pin EMPTY (attenuate-without-sink; zero-authority skip);
/// - the X-C9 basis pin: `Tri { alpha, beta, gamma }`, restrict(beta) → actual=2 — bit =
///   authority DECL index (registries.rs `enumerate()`), so a reversed/sorted basis diffs
///   exactly here;
/// - MI-2 (order): source order == block-Vec obligation order through if/else+join AND
///   while+after (the two pinned CF shapes) — no corpus fencing needed for these;
/// - MI-3: an un-annotated cap let (`let r = f.restrict(burn)`) obligates identically —
///   the shadow's env needs RHS-form cap inference for exactly this shape.
const CAP_WORKLOAD_CORPUS: &[(&str, &str, &str)] = &[
    (
        "w_atten_call",
        "module sigil;\ncap type Fuel { burn, query }\nfn needs(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return needs(r); }\n",
        "Call Fuel 3 1",
    ),
    (
        "w_atten_return",
        "module sigil;\ncap type Fuel { burn, query }\nfn pass(f: Fuel) -> Fuel { let g: Fuel = f.restrict(burn); return g; }\n",
        "Return Fuel 3 1",
    ),
    (
        "w_atten_send",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(seed: i64) {}\n    on Burn(f: Fuel) {}\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(worker: ActorRef<Worker>) -> i64 {\n        worker.send(Burn(fuel.restrict(burn)));\n        return 1;\n    }\n}\n",
        "Serialize Fuel 3 1",
    ),
    (
        "w_spawn_clean",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(f: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 {\n        let child_fuel: Fuel = fuel.split(50);\n        let _child = spawn::<Worker>(child_fuel);\n        return 1;\n    }\n}\n",
        "Spawn Fuel 3 3",
    ),
    (
        "w_atten_nosink",
        "module sigil;\ncap type Fuel { burn, query }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return 0; }\n",
        "",
    ),
    (
        "w_zero_auth",
        "module sigil;\ncap type Token { }\nfn take(t: Token) -> i64 { return 1; }\nfn go(t: Token) -> i64 { return take(t); }\n",
        "",
    ),
    (
        "w_basis3_mid",
        "module sigil;\ncap type Tri { alpha, beta, gamma }\nfn need(t: Tri) -> i64 { return 1; }\nfn go(t: Tri) -> i64 { let r: Tri = t.restrict(beta); return need(r); }\n",
        "Call Tri 7 2",
    ),
    (
        "w_shadow_rebind",
        "module sigil;\ncap type Fuel { burn, query }\nfn use_it(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let x: i64 = use_it(f); let f: Fuel = f.restrict(burn); return use_it(f); }\n",
        "Call Fuel 3 3\nCall Fuel 3 1",
    ),
    (
        "w_cf_if_join",
        "module sigil;\ncap type Fuel { burn, query }\nfn s(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, b: bool) -> i64 {\n    let r: Fuel = f.restrict(burn);\n    if b {\n        let x: i64 = s(f);\n    } else {\n        let y: i64 = s(r);\n    }\n    let z: i64 = s(f);\n    return z;\n}\n",
        "Call Fuel 3 3\nCall Fuel 3 1\nCall Fuel 3 3",
    ),
    (
        "w_cf_while",
        "module sigil;\ncap type Fuel { burn, query }\nfn s(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, n: i64) -> i64 {\n    let r: Fuel = f.restrict(query);\n    let mut i: i64 = 0;\n    while i < n {\n        let x: i64 = s(r);\n        i = i + 1;\n    }\n    let z: i64 = s(f);\n    return z;\n}\n",
        "Call Fuel 3 2\nCall Fuel 3 3",
    ),
    (
        "w_unannotated_let",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r = f.restrict(burn); return need(r); }\n",
        "Call Fuel 3 1",
    ),
    // Sweep folds (Phase-0 adversarial sweep, all pinned first-try):
    // chained restricts AND-accumulate (3 & 1 & 2 = 0); a multi-cap call emits one
    // obligation PER ARG in arg order (and gamma = bit 2 re-pins the decl basis); a
    // call-RETURNED cap is an opaque source (terminates at full — the Return-sink check is
    // what makes that sound inter-procedurally); draw preserves like split.
    (
        "w_chain_restrict_zero",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a: Fuel = f.restrict(burn); let b: Fuel = a.restrict(query); return need(b); }\n",
        "Call Fuel 3 0",
    ),
    (
        "w_two_caps_one_call",
        "module sigil;\ncap type Fuel { burn, query }\ncap type Tri { alpha, beta, gamma }\nfn need2(a: Fuel, b: Tri) -> i64 { return 1; }\nfn go(f: Fuel, t: Tri) -> i64 { let r: Tri = t.restrict(gamma); return need2(f, r); }\n",
        "Call Fuel 3 3\nCall Tri 7 4",
    ),
    (
        "w_through_return_opaque",
        "module sigil;\ncap type Fuel { burn, query }\nfn pass(f: Fuel) -> Fuel { return f; }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let g: Fuel = pass(f); return need(g); }\n",
        "Return Fuel 3 3\nCall Fuel 3 3\nCall Fuel 3 3",
    ),
    (
        "w_draw_preserves",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let d: Fuel = f.draw(10); return need(d); }\n",
        "Call Fuel 3 3",
    ),
];

/// CAP-0: the oracle's obligation workload matches the pinned frozen render on every
/// corpus fixture. These pins ARE the ground truth the selfhost shadow (CAP-1/2) will be
/// diffed against — an oracle-side collector change surfaces here first.
#[test]
fn cap0_workload_pins() {
    for (label, src, expected) in CAP_WORKLOAD_CORPUS {
        let w = cap_workload_oracle(label, src);
        assert_eq!(
            render_workload(&w),
            *expected,
            "SH-CAP {label}: the oracle workload drifted from the CAP-0 pin:\n{src}"
        );
    }
}

/// Capability parameters do not carry per-callee authority subsets. Even a callee that ignores its
/// argument requires the capability type's full declared mask; this is deliberate conservative
/// rejection, not an inferred contract from the callee body.
#[test]
fn cap_sink_contract_is_deliberately_full_mask() {
    let restricted = cap_workload_oracle(
        "full-mask-restricted",
        "module sigil; cap type Tri { alpha, beta, gamma } fn ignores(t: Tri) -> i64 { return 0; } fn go(t: Tri) -> i64 { let r: Tri = t.restrict(alpha); return ignores(r); }",
    );
    assert_eq!(restricted.obligations.len(), 1);
    let restricted = &restricted.obligations[0];
    assert_eq!(restricted.required_mask, 0b111);
    assert_eq!(restricted.actual_mask, 0b001);

    let full = cap_workload_oracle(
        "full-mask-control",
        "module sigil; cap type Tri { alpha, beta, gamma } fn ignores(t: Tri) -> i64 { return 0; } fn go(t: Tri) -> i64 { return ignores(t); }",
    );
    assert_eq!(full.obligations.len(), 1);
    let full = &full.obligations[0];
    assert_eq!(full.required_mask, 0b111);
    assert_eq!(full.actual_mask, 0b111);
}

/// X-C6 fence: capability LINEARITY (T043) makes the oracle's flow-insensitive
/// last-def-wins auth-source map unobservable from type-clean source — a cap var cannot be
/// reassigned, so every cap VarId is single-def and a forward binding env is provably
/// equivalent. The CAP-2 shadow leans on that simplification; if linearity is ever relaxed,
/// this test fires and the flow-free assumption MUST be revisited (the reassign shape below
/// would then pin the oracle's `use(c)`-sees-the-LATER-restrict behavior instead).
#[test]
fn cap0_linearity_makes_trace_flow_free() {
    let src = "module sigil;\ncap type Fuel { burn, query }\nfn use_it(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let mut c: Fuel = f; let x: i64 = use_it(c); c = c.restrict(burn); return x; }\n";
    let source = SourceFile::new("<cap-diff>", src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(pdiags.is_empty(), "the T043 fence fixture must parse");
    let resolved = name_resolution::resolve(&ast).expect("the T043 fence fixture must resolve");
    let err = type_check::check_with_options(&resolved, &CompileOptions::default())
        .expect_err("cap reassignment must be type-REJECTED (linearity)");
    assert!(
        err.iter().any(|d| d.code().as_str() == "T043"),
        "expected T043 (linear cap assign) in {:?}",
        err.iter().map(|d| d.code().to_string()).collect::<Vec<_>>()
    );
}

/// Determinism: the collector's obligation order is byte-stable across runs (NC6) — two
/// oracle runs render identically on every fixture.
#[test]
fn cap0_workload_deterministic() {
    for (label, src, _) in CAP_WORKLOAD_CORPUS {
        let a = render_workload(&cap_workload_oracle(label, src));
        let b = render_workload(&cap_workload_oracle(label, src));
        assert_eq!(
            a, b,
            "SH-CAP {label}: oracle workload must be deterministic"
        );
    }
}

// ── CAP-1: the selfhost shadow lane ────────────────────────────────────────────────────
//
// Composes lexer + parser + typecheck + cap_check into one tool emitting a `;`-joined
// `{kind} {cap} {required};` stream. The shadow covers Call + Return sinks (bare-name cap
// args); Spawn/Serialize are DEFERRED (their cap arg is not a bare-name path). Compared
// EXACTLY (order-preserving, no dedup — MI-2) against the oracle workload projected to the
// required mask over the covered sub-corpus.

/// Strip the per-file `module X;` headers into one `module tool;` calling `cap_encode`.
fn cap_tool(body: &str) -> String {
    let lexer_defs = LEXER.replace("\nmodule lexer;\n", "\n");
    let parser_defs = PARSER.replace("\nmodule parser;\n", "\n");
    let tc_defs = TYPECHECK.replace("\nmodule typecheck;\n", "\n");
    let cap_defs = CAPCHECK.replace("\nmodule cap_check;\n", "\n");
    format!(
        "module tool;\n{lexer_defs}\n{parser_defs}\n{tc_defs}\n{cap_defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn cap_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = cap_encode(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

fn cap_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        compile_tool(&cap_tool(cap_body()))
            .expect("cap_check tool should compile")
            .wasm
    })
}

/// The shadow's FULL obligation list: the `;`-joined `{kind} {cap} {required} {actual}` stream
/// split, empties dropped (order kept — no dedup, no sort).
fn sigil_full(src: &str) -> Vec<String> {
    let result = execute_ephemeral(cap_wasm(), src.as_bytes(), CAP_FUEL, &IoGrants::none())
        .expect("cap_check tool executes");
    let out = String::from_utf8(result.output).expect("tool output is UTF-8");
    out.split(';')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect()
}

/// The shadow's obligation list projected to `{kind} {cap} {required}` (the CAP-1 view — drop the
/// CAP-2 `actual` field so the required lane is pinned in isolation).
fn sigil_required(src: &str) -> Vec<String> {
    sigil_full(src)
        .iter()
        .map(|o| {
            let toks: Vec<&str> = o.split(' ').collect();
            format!("{} {} {}", toks[0], toks[1], toks[2])
        })
        .collect()
}

/// The oracle workload projected to `{kind:?} {cap} {required}` per obligation, program order.
fn oracle_required(label: &str, src: &str) -> Vec<String> {
    cap_workload_oracle(label, src)
        .obligations
        .iter()
        .map(|o| format!("{:?} {} {}", o.kind, o.cap_type, o.required_mask))
        .collect()
}

/// The FULL oracle workload `{kind:?} {cap} {required} {actual}` per obligation, program order
/// (CAP-2). This is the frozen render minus var_id (X-C7).
fn oracle_full(label: &str, src: &str) -> Vec<String> {
    cap_workload_oracle(label, src)
        .obligations
        .iter()
        .map(|o| {
            format!(
                "{:?} {} {} {}",
                o.kind, o.cap_type, o.required_mask, o.actual_mask
            )
        })
        .collect()
}

/// The CAP-1 covered sub-corpus: only Call + Return sinks (bare-name cap args). Each fixture is
/// parse-clean on BOTH front-ends and holds no Spawn/Serialize sink (asserted below).
const CAP1_COVERED: &[(&str, &str)] = &[
    (
        "w_atten_call",
        "module sigil;\ncap type Fuel { burn, query }\nfn needs(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return needs(r); }\n",
    ),
    (
        "w_atten_return",
        "module sigil;\ncap type Fuel { burn, query }\nfn pass(f: Fuel) -> Fuel { let g: Fuel = f.restrict(burn); return g; }\n",
    ),
    (
        "w_atten_nosink",
        "module sigil;\ncap type Fuel { burn, query }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return 0; }\n",
    ),
    (
        "w_zero_auth",
        "module sigil;\ncap type Token { }\nfn take(t: Token) -> i64 { return 1; }\nfn go(t: Token) -> i64 { return take(t); }\n",
    ),
    (
        "w_basis3_mid",
        "module sigil;\ncap type Tri { alpha, beta, gamma }\nfn need(t: Tri) -> i64 { return 1; }\nfn go(t: Tri) -> i64 { let r: Tri = t.restrict(beta); return need(r); }\n",
    ),
    (
        "w_shadow_rebind",
        "module sigil;\ncap type Fuel { burn, query }\nfn use_it(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let x: i64 = use_it(f); let f: Fuel = f.restrict(burn); return use_it(f); }\n",
    ),
    (
        "w_cf_if_join",
        "module sigil;\ncap type Fuel { burn, query }\nfn s(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, b: bool) -> i64 {\n    let r: Fuel = f.restrict(burn);\n    if b {\n        let x: i64 = s(f);\n    } else {\n        let y: i64 = s(r);\n    }\n    let z: i64 = s(f);\n    return z;\n}\n",
    ),
    (
        "w_cf_while",
        "module sigil;\ncap type Fuel { burn, query }\nfn s(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, n: i64) -> i64 {\n    let r: Fuel = f.restrict(query);\n    let mut i: i64 = 0;\n    while i < n {\n        let x: i64 = s(r);\n        i = i + 1;\n    }\n    let z: i64 = s(f);\n    return z;\n}\n",
    ),
    (
        "w_unannotated_let",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r = f.restrict(burn); return need(r); }\n",
    ),
    (
        "w_chain_restrict_zero",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a: Fuel = f.restrict(burn); let b: Fuel = a.restrict(query); return need(b); }\n",
    ),
    (
        "w_two_caps_one_call",
        "module sigil;\ncap type Fuel { burn, query }\ncap type Tri { alpha, beta, gamma }\nfn need2(a: Fuel, b: Tri) -> i64 { return 1; }\nfn go(f: Fuel, t: Tri) -> i64 { let r: Tri = t.restrict(gamma); return need2(f, r); }\n",
    ),
    (
        "w_through_return_opaque",
        "module sigil;\ncap type Fuel { burn, query }\nfn pass(f: Fuel) -> Fuel { return f; }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let g: Fuel = pass(f); return need(g); }\n",
    ),
    (
        "w_draw_preserves",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let d: Fuel = f.draw(10); return need(d); }\n",
    ),
    // MI-4: the function census must span actor handlers, not just module fns.
    (
        "w_actor_handler_call",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return need(r); }\n}\n",
    ),
    // Sweep folds (Phase-0 adversarial sweep, all matched first-try):
    // a 4-authority cap exercises full_mask beyond the corpus max (15); a 1-authority cap
    // pins the narrowest non-zero mask; mixed args prove only the cap arg emits; actor init
    // extends the MI-4 census to init blocks; a nested call proves the inner sink emits.
    (
        "w_four_auth",
        "module sigil;\ncap type Quad { a, b, c, d }\nfn need(q: Quad) -> i64 { return 1; }\nfn go(q: Quad) -> i64 { let r: Quad = q.restrict(c); return need(r); }\n",
    ),
    (
        "w_one_auth",
        "module sigil;\ncap type Solo { only }\nfn need(s: Solo) -> i64 { return 1; }\nfn go(s: Solo) -> i64 { return need(s); }\n",
    ),
    (
        "w_mixed_args",
        "module sigil;\ncap type Fuel { burn, query }\nfn m(a: i64, f: Fuel, b: i64) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { return m(7, f, 9); }\n",
    ),
    (
        "w_actor_init_call",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nactor Worker {\n    init(f: Fuel) { let r: Fuel = f.restrict(burn); let x: i64 = need(r); }\n    on Ping() -> i64 { return 0; }\n}\nentry actor Main {\n    on Start() -> i64 { return 1; }\n}\n",
    ),
    (
        "w_nested_call",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn wrap(n: i64) -> i64 { return n; }\nfn go(f: Fuel) -> i64 { return wrap(need(f)); }\n",
    ),
    // CAP-2 authority-trace folds (Phase-0 sweep, all matched first-try):
    // restrict on a HIGH bit (Quad restrict(d) -> bit 8); split-then-restrict composes
    // preserve then narrow (3 -> 3 -> 1); a bare-name copy follows its src (the Assign(Var)
    // arm, actual=3); draw-then-restrict (draw preserves, then narrow to query=2).
    (
        "w_restrict_high_bit",
        "module sigil;\ncap type Quad { a, b, c, d }\nfn need(q: Quad) -> i64 { return 1; }\nfn go(q: Quad) -> i64 { let r: Quad = q.restrict(d); return need(r); }\n",
    ),
    (
        "w_split_then_restrict",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a: Fuel = f.split(50); let b: Fuel = a.restrict(burn); return need(b); }\n",
    ),
    (
        "w_copy_binding",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f; return need(r); }\n",
    ),
    (
        "w_draw_then_restrict",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a: Fuel = f.draw(3); let b: Fuel = a.restrict(query); return need(b); }\n",
    ),
    // CAP-4: the Spawn + Serialize sinks (state fields seeded at full; .send/.ask are P_K_SEND/
    // P_K_ASK carrying a message ctor whose args are the serialized caps).
    (
        "w_spawn_full",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(f: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { let c: Fuel = fuel.split(50); let _w = spawn::<Worker>(c); return 1; }\n}\n",
    ),
    (
        "w_spawn_attenuated",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(f: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { let c: Fuel = fuel.restrict(burn); let _w = spawn::<Worker>(c); return 1; }\n}\n",
    ),
    (
        "w_spawn_two_caps",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(a: Fuel, b: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { let c: Fuel = fuel.split(50); let d: Fuel = fuel.restrict(burn); let _w = spawn::<Worker>(c, d); return 1; }\n}\n",
    ),
    (
        "w_send_attenuated",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(seed: i64) {}\n    on Burn(f: Fuel) {}\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(worker: ActorRef<Worker>) -> i64 { let r: Fuel = fuel.restrict(burn); worker.send(Burn(r)); return 1; }\n}\n",
    ),
    (
        "w_send_state_direct",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(seed: i64) {}\n    on Burn(f: Fuel) {}\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(worker: ActorRef<Worker>) -> i64 { worker.send(Burn(fuel)); return 1; }\n}\n",
    ),
    (
        "w_ask_attenuated",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(seed: i64) {}\n    on Q(f: Fuel) -> i64 { return 0; }\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(worker: ActorRef<Worker>) -> i64 { let r: Fuel = fuel.restrict(burn); let x: i64 = worker.ask(Q(r), 5000); return x; }\n}\n",
    ),
];

/// CAP-1: the selfhost required-mask projection equals the oracle's, EXACTLY and in program
/// order, over the Call/Return covered corpus.
#[test]
fn cap1_required_parity() {
    for (label, src) in CAP1_COVERED {
        let oracle = oracle_required(label, src);
        assert_eq!(
            sigil_required(src),
            oracle,
            "SH-CAP {label}: the selfhost required projection must match the oracle:\n{src}"
        );
    }
}

/// CAP-2: the selfhost FULL workload (`{kind} {cap} {required} {actual}`) equals the oracle's,
/// EXACTLY and in program order, over the Call/Return covered corpus. This is the epic's core —
/// the static authority trace (restrict narrows, split/draw/copy preserve, opaque→full).
#[test]
fn cap2_workload_parity() {
    for (label, src) in CAP1_COVERED {
        let oracle = oracle_full(label, src);
        assert_eq!(
            sigil_full(src),
            oracle,
            "SH-CAP {label}: the selfhost full workload must match the oracle:\n{src}"
        );
    }
}

/// Non-stub: the shadow produces at least two DISTINCT streams across the covered corpus (a
/// constant emitter — e.g. always-"" or always-one-line — is caught here).
#[test]
fn cap1_non_stub() {
    let mut streams: std::collections::BTreeSet<Vec<String>> = std::collections::BTreeSet::new();
    for (_, src) in CAP1_COVERED {
        streams.insert(sigil_required(src));
    }
    assert!(
        streams.len() >= 2,
        "SH-CAP: the shadow is a stub — all covered fixtures produced the same stream"
    );
}

/// Determinism: two runs of the compiled shadow render identically (per fixture).
#[test]
fn cap1_shadow_deterministic() {
    for (_, src) in CAP1_COVERED {
        assert_eq!(
            sigil_required(src),
            sigil_required(src),
            "SH-CAP: the shadow must be deterministic:\n{src}"
        );
    }
}

// ── CAP-3: the verdict lane (bitwise C003) + the accept floor (epic close) ──────────────
//
// The shadow's `cap_verdict_encode` emits `C003;` per VIOLATED obligation (the callee-blind
// bitwise rule `actual & required != required`). On slot-free programs that rule is provably
// == the Z3 discharge's C003 (the CAP-0 equivalence proof, on the solver CI lane); C002/C004/
// C005 stay Z3-only. This lane is structurally solver-free: the oracle side derives its C003
// verdict from the (Z3-free) Pure collector workload by the same bitwise rule.

fn cap_verdict_body() -> &'static str {
    "    let opt: Option<str> = input_ptr.from_bytes(input_len);\n\
     \x20   let src: str = opt.unwrap_or(\"\");\n\
     \x20   let toks: Vec<Token> = lex(src);\n\
     \x20   let mut nodes: Arena<PNode> = Arena::new();\n\
     \x20   let mut kids: Vec<i64> = Vec::new();\n\
     \x20   let root: i64 = parser_parse(src, toks, nodes, kids);\n\
     \x20   let enc: str = cap_verdict_encode(nodes, kids, root);\n\
     \x20   return enc.as_output();"
}

fn cap_verdict_wasm() -> &'static [u8] {
    static W: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        compile_tool(&cap_tool(cap_verdict_body()))
            .expect("cap_verdict tool should compile")
            .wasm
    })
}

/// The shadow's verdict: the `C003;`-joined stream split (one per violated sink, program order).
fn sigil_verdict(src: &str) -> Vec<String> {
    let result = execute_ephemeral(
        cap_verdict_wasm(),
        src.as_bytes(),
        CAP_FUEL,
        &IoGrants::none(),
    )
    .expect("cap_verdict tool executes");
    let out = String::from_utf8(result.output).expect("tool output is UTF-8");
    out.split(';')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect()
}

/// The oracle's verdict, derived Z3-free from the Pure collector workload by the bitwise rule
/// (== the Z3 C003 on slot-free programs — proven on the solver lane).
fn oracle_verdict(label: &str, src: &str) -> Vec<String> {
    cap_workload_oracle(label, src)
        .obligations
        .iter()
        .filter(|o| o.actual_mask & o.required_mask != o.required_mask)
        .map(|_| "C003".to_string())
        .collect()
}

/// CAP-3: the selfhost verdict equals the oracle's over the full covered corpus (a mix of
/// violated and satisfied sinks) — the epic's capstone parity.
#[test]
fn cap3_verdict_parity() {
    for (label, src) in CAP1_COVERED {
        assert!(
            !src.contains("Slot"),
            "SH-CAP {label}: the verdict corpus must stay slot-free (X-C3)"
        );
        assert_eq!(
            sigil_verdict(src),
            oracle_verdict(label, src),
            "SH-CAP {label}: the selfhost C003 verdict must match the oracle:\n{src}"
        );
    }
}

/// CAP-3 reject corpus: attenuated caps reaching sinks. The oracle's C003 count is PINNED per
/// fixture (ring-style), and the shadow matches it. required is always full (callee-blind), so any
/// narrowed authority at a sink violates.
const CAP3_REJECT: &[(&str, &str, usize)] = &[
    (
        "r_restrict_call",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return need(r); }\n",
        1,
    ),
    (
        "r_restrict_return",
        "module sigil;\ncap type Fuel { burn, query }\nfn pass(f: Fuel) -> Fuel { let g: Fuel = f.restrict(burn); return g; }\n",
        1,
    ),
    (
        "r_chain_to_zero",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a: Fuel = f.restrict(burn); let b: Fuel = a.restrict(query); return need(b); }\n",
        1,
    ),
    (
        "r_two_violations",
        "module sigil;\ncap type Fuel { burn, query }\nfn a(f: Fuel) -> i64 { return 1; }\nfn b(f: Fuel) -> i64 { return 2; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); let x: i64 = a(r); return b(r); }\n",
        2,
    ),
    (
        "r_mixed_arity",
        "module sigil;\ncap type Tri { alpha, beta, gamma }\nfn need(t: Tri) -> i64 { return 1; }\nfn go(t: Tri) -> i64 { let r: Tri = t.restrict(beta); return need(r); }\n",
        1,
    ),
    (
        "r_actor_handler",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return need(r); }\n}\n",
        1,
    ),
    // Sweep fold: one violated sink (restricted r) + one clean sink (full f) in the same fn — the
    // per-sink verdict fires exactly once.
    (
        "r_mixed_violation_accept",
        "module sigil;\ncap type Fuel { burn, query }\nfn a(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); let x: i64 = a(r); return a(f); }\n",
        1,
    ),
    // CAP-4: attenuated caps reaching Spawn / Serialize sinks.
    (
        "r_spawn_attenuated",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(f: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { let c: Fuel = fuel.restrict(burn); let _w = spawn::<Worker>(c); return 1; }\n}\n",
        1,
    ),
    (
        "r_send_attenuated",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(seed: i64) {}\n    on Burn(f: Fuel) {}\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(worker: ActorRef<Worker>) -> i64 { let r: Fuel = fuel.restrict(burn); worker.send(Burn(r)); return 1; }\n}\n",
        1,
    ),
];

/// CAP-3 accept corpus: caps reach sinks at FULL authority (params direct, split/draw preserve,
/// copies), or never reach a sink. Zero C003 on BOTH sides.
const CAP3_ACCEPT: &[(&str, &str)] = &[
    (
        "a_param_direct",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { return need(f); }\n",
    ),
    (
        "a_split_preserves",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let c: Fuel = f.split(50); return need(c); }\n",
    ),
    (
        "a_draw_preserves",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let d: Fuel = f.draw(3); return need(d); }\n",
    ),
    (
        "a_copy_preserves",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f; return need(r); }\n",
    ),
    (
        "a_attenuate_no_sink",
        "module sigil;\ncap type Fuel { burn, query }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return 0; }\n",
    ),
    (
        "a_zero_authority",
        "module sigil;\ncap type Token { }\nfn take(t: Token) -> i64 { return 1; }\nfn go(t: Token) -> i64 { return take(t); }\n",
    ),
    // Sweep fold: restricting a 1-authority cap to its ONLY authority keeps FULL authority
    // (1 == full) — an accept. A naive "any restrict is a C003" verdict wrongly rejects this.
    (
        "a_one_auth_restrict_full",
        "module sigil;\ncap type Solo { only }\nfn need(s: Solo) -> i64 { return 1; }\nfn go(s: Solo) -> i64 { let r: Solo = s.restrict(only); return need(r); }\n",
    ),
    // CAP-4: full-authority caps reaching Spawn / Serialize sinks (split preserves; a state cap
    // sent directly is at full).
    (
        "a_spawn_full",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(f: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 { let c: Fuel = fuel.split(50); let _w = spawn::<Worker>(c); return 1; }\n}\n",
    ),
    (
        "a_send_state_direct",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(seed: i64) {}\n    on Burn(f: Fuel) {}\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(worker: ActorRef<Worker>) -> i64 { worker.send(Burn(fuel)); return 1; }\n}\n",
    ),
];

/// The shadow's C003 count matches the pinned oracle count on every reject fixture (ring-style).
#[test]
fn cap3_reject_matches_oracle() {
    for (label, src, expected) in CAP3_REJECT {
        let oracle = oracle_verdict(label, src);
        assert_eq!(
            oracle.len(),
            *expected,
            "SH-CAP {label}: the oracle must emit the pinned C003 count:\n{src}"
        );
        assert_eq!(
            sigil_verdict(src),
            oracle,
            "SH-CAP {label}: the selfhost verdict must match the oracle:\n{src}"
        );
    }
}

/// The accept floor: zero C003 on both sides for every full-authority / no-sink fixture.
#[test]
fn cap3_accept_clean_both_sides() {
    for (label, src) in CAP3_ACCEPT {
        assert!(
            oracle_verdict(label, src).is_empty(),
            "SH-CAP {label}: the oracle must be C003-clean:\n{src}"
        );
        assert!(
            sigil_verdict(src).is_empty(),
            "SH-CAP {label}: the selfhost verdict must be C003-clean:\n{src}"
        );
    }
}

/// Non-stub: the verdict lane produces both non-empty AND empty streams (a constant emitter is
/// caught) — the reject corpus fires, the accept corpus stays clean.
#[test]
fn cap3_verdict_non_stub() {
    let any_reject = CAP3_REJECT
        .iter()
        .any(|(_, src, _)| !sigil_verdict(src).is_empty());
    let all_accept_clean = CAP3_ACCEPT
        .iter()
        .all(|(_, src)| sigil_verdict(src).is_empty());
    assert!(any_reject, "SH-CAP: the verdict lane never fires (stub)");
    assert!(
        all_accept_clean,
        "SH-CAP: the verdict lane over-fires on accepts"
    );
}
