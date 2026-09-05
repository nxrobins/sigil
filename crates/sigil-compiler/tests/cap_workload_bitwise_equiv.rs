//! SH-CAP CAP-0: the bitwise-verdict ⇔ Z3-C003 equivalence proof.
//!
//! The SH-CAP differential lane (`sigil-runtime/tests/cap_workload_differential.rs`) is
//! structurally solver-free (sigil-runtime builds sigil-compiler with
//! `default-features = false`). Its verdict lane (CAP-3) will predict C003 per obligation
//! by the BITWISE rule `actual & required != required`. That prediction is sound only if
//! the bitwise rule agrees with the Z3 discharge on the covered (slot-free) corpus — the
//! collector's own doc warns the static trace diverges from Z3 exactly at slot-meet
//! (`SlotTake`). This test IS that agreement proof, and it lives here — under
//! `cfg(feature = "solver")`, on the solver CI lane — because the runtime harness never
//! has Z3.
//!
//! Also carries the X-C4 boundary assert: on the covered corpus the oracle emits ONLY
//! C003 (never C002/C004/C005) — a fixture that trips the Z3-only codes is rejected at
//! add time, keeping the shadow's claim honest.
#![cfg(feature = "solver")]

use sigil_compiler::CompileOptions;
use sigil_compiler::air;
use sigil_compiler::air_capability_v2;
use sigil_compiler::capability;
use sigil_compiler::name_resolution;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;
use sigil_compiler::type_check;

/// Mirrors the runtime lane's CAP_WORKLOAD_CORPUS (the slot-free covered surface).
/// (label, fixture, expected C003 count).
const EQUIV_CORPUS: &[(&str, &str, usize)] = &[
    (
        "w_atten_call",
        "module sigil;\ncap type Fuel { burn, query }\nfn needs(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return needs(r); }\n",
        1,
    ),
    (
        "w_atten_return",
        "module sigil;\ncap type Fuel { burn, query }\nfn pass(f: Fuel) -> Fuel { let g: Fuel = f.restrict(burn); return g; }\n",
        1,
    ),
    (
        "w_atten_send",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(seed: i64) {}\n    on Burn(f: Fuel) {}\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start(worker: ActorRef<Worker>) -> i64 {\n        worker.send(Burn(fuel.restrict(burn)));\n        return 1;\n    }\n}\n",
        1,
    ),
    (
        "w_spawn_clean",
        "module sigil;\ncap type Fuel { burn, query }\nactor Worker {\n    init(f: Fuel) {}\n    on Ping() -> i64 { return 0; }\n}\nentry actor Main {\n    state { fuel: Fuel }\n    on Start() -> i64 {\n        let child_fuel: Fuel = fuel.split(50);\n        let _child = spawn::<Worker>(child_fuel);\n        return 1;\n    }\n}\n",
        0,
    ),
    (
        "w_atten_nosink",
        "module sigil;\ncap type Fuel { burn, query }\nfn go(f: Fuel) -> i64 { let r: Fuel = f.restrict(burn); return 0; }\n",
        0,
    ),
    (
        "w_zero_auth",
        "module sigil;\ncap type Token { }\nfn take(t: Token) -> i64 { return 1; }\nfn go(t: Token) -> i64 { return take(t); }\n",
        0,
    ),
    (
        "w_basis3_mid",
        "module sigil;\ncap type Tri { alpha, beta, gamma }\nfn need(t: Tri) -> i64 { return 1; }\nfn go(t: Tri) -> i64 { let r: Tri = t.restrict(beta); return need(r); }\n",
        1,
    ),
    (
        "w_shadow_rebind",
        "module sigil;\ncap type Fuel { burn, query }\nfn use_it(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let x: i64 = use_it(f); let f: Fuel = f.restrict(burn); return use_it(f); }\n",
        1,
    ),
    (
        "w_cf_if_join",
        "module sigil;\ncap type Fuel { burn, query }\nfn s(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, b: bool) -> i64 {\n    let r: Fuel = f.restrict(burn);\n    if b {\n        let x: i64 = s(f);\n    } else {\n        let y: i64 = s(r);\n    }\n    let z: i64 = s(f);\n    return z;\n}\n",
        1,
    ),
    (
        "w_cf_while",
        "module sigil;\ncap type Fuel { burn, query }\nfn s(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel, n: i64) -> i64 {\n    let r: Fuel = f.restrict(query);\n    let mut i: i64 = 0;\n    while i < n {\n        let x: i64 = s(r);\n        i = i + 1;\n    }\n    let z: i64 = s(f);\n    return z;\n}\n",
        1,
    ),
    (
        "w_unannotated_let",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let r = f.restrict(burn); return need(r); }\n",
        1,
    ),
    (
        "w_chain_restrict_zero",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let a: Fuel = f.restrict(burn); let b: Fuel = a.restrict(query); return need(b); }\n",
        1,
    ),
    (
        "w_two_caps_one_call",
        "module sigil;\ncap type Fuel { burn, query }\ncap type Tri { alpha, beta, gamma }\nfn need2(a: Fuel, b: Tri) -> i64 { return 1; }\nfn go(f: Fuel, t: Tri) -> i64 { let r: Tri = t.restrict(gamma); return need2(f, r); }\n",
        1,
    ),
    (
        "w_through_return_opaque",
        "module sigil;\ncap type Fuel { burn, query }\nfn pass(f: Fuel) -> Fuel { return f; }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let g: Fuel = pass(f); return need(g); }\n",
        0,
    ),
    (
        "w_draw_preserves",
        "module sigil;\ncap type Fuel { burn, query }\nfn need(f: Fuel) -> i64 { return 1; }\nfn go(f: Fuel) -> i64 { let d: Fuel = f.draw(10); return need(d); }\n",
        0,
    ),
];

/// On every slot-free covered fixture: the bitwise rule over the Pure collector's
/// workload predicts EXACTLY the Z3 discharge's C003 count, and the oracle emits no
/// Z3-only codes (C002/C004/C005) — the X-C4 boundary.
#[test]
fn cap0_bitwise_verdict_matches_z3_c003() {
    for (label, src, expected_c003) in EQUIV_CORPUS {
        // X-C3: the equivalence claim is scoped slot-free — enforce it structurally.
        assert!(
            !src.contains("Slot"),
            "SH-CAP {label}: the equivalence corpus must stay slot-free (X-C3)"
        );

        let source = SourceFile::new("<cap-equiv>", *src);
        let (ast, pdiags) = parser::parse(&source);
        assert!(pdiags.is_empty(), "SH-CAP {label}: fixture must parse");
        let resolved = name_resolution::resolve(&ast).expect("fixture must resolve");
        let (typed, registry) =
            type_check::check_with_options(&resolved, &CompileOptions::default())
                .unwrap_or_else(|e| panic!("SH-CAP {label}: fixture must type-check: {e:?}"));
        let lowered = air::lower(&typed);

        // The bitwise prediction from the Pure collector's workload.
        let (_, workload) =
            air_capability_v2::collect_air_capability_workload_for_test(&lowered, &registry);
        let bitwise: usize = workload
            .obligations
            .iter()
            .filter(|o| o.actual_mask & o.required_mask != o.required_mask)
            .count();
        assert_eq!(
            bitwise, *expected_c003,
            "SH-CAP {label}: bitwise prediction drifted from the pin"
        );

        // The Z3 discharge's verdict (capability::verify runs structural + v2 under the
        // solver feature).
        let codes: Vec<String> = match capability::verify(&lowered, &registry) {
            Ok(_) => Vec::new(),
            Err(ds) => ds.iter().map(|d| d.code().to_string()).collect(),
        };
        let c003 = codes.iter().filter(|c| c.as_str() == "C003").count();
        let z3_only: Vec<&String> = codes
            .iter()
            .filter(|c| matches!(c.as_str(), "C002" | "C004" | "C005"))
            .collect();
        assert!(
            z3_only.is_empty(),
            "SH-CAP {label}: X-C4 — the covered corpus must not trip Z3-only codes, got {z3_only:?}"
        );
        assert_eq!(
            bitwise, c003,
            "SH-CAP {label}: bitwise-from-workload must equal the Z3 C003 count (slot-free), oracle codes: {codes:?}"
        );
    }
}
