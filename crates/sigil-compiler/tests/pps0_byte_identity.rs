//! PPS-0 byte-identity invariants. Admitting `mut Map` state touched the
//! shared alloc path (`BumpAlloc` gained a `persistent` flag, record
//! constructs consult it, associated functions inherit the state coloring),
//! so the P1/P2 guarantees need explicit pins:
//!
//! - a module with NO actor state emits no `alloc_persistent` import and no
//!   `$state` instance — every existing tool, the bench corpus, and the
//!   self-host image lower byte-identically;
//! - compilation stays deterministic (I6) with state maps in play;
//! - ordinary (non-state) `Map`/`Vec` use is unchanged by the presence of a
//!   state map elsewhere in the same module.

use sigil_compiler::{compile_module, compile_tool};

/// A tool: no actors, so no actor state anywhere.
const STATE_FREE_MAP_TOOL: &str = r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let m: Map<i64, i64> = Map::new();
    m.insert(1, 10);
    m.insert(2, 20);
    let mut i: i64 = 0;
    while i < 20 {
        m.insert(i + 3, i * 5);
        i = i + 1;
    }
    return m.get_or(2, 0);
}
"#;

/// The same heavy `Map` workload inside an ACTOR with no `mut` state — the
/// AIR-visible form of the state-free invariant.
const STATE_FREE_MAP_ACTOR: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let m: Map<i64, i64> = Map::new();
        m.insert(1, 10);
        let mut i: i64 = 0;
        while i < 20 {
            m.insert(i + 3, i * 5);
            i = i + 1;
        }
        return m.get_or(1, 0);
    }
}
"#;

#[test]
fn state_free_module_has_no_persistent_alloc_or_state_instance() {
    let compiled = compile_module(STATE_FREE_MAP_ACTOR).expect("state-free map actor compiles");
    // No `$state` monomorph instance anywhere.
    let state_instances: Vec<&str> = compiled
        .air
        .functions
        .iter()
        .map(|f| f.name.as_str())
        .filter(|name| name.ends_with("$state"))
        .collect();
    assert!(
        state_instances.is_empty(),
        "a state-free module must emit no state-backed instances; got {state_instances:?}"
    );
    // And no persistent allocation of either kind.
    let has_persistent = compiled.air.functions.iter().any(|f| {
        f.blocks.iter().any(|b| {
            b.stmts.iter().any(|s| {
                matches!(
                    s,
                    sigil_compiler::air::AirStmt::IntrinsicAlloc {
                        persistent: true,
                        ..
                    } | sigil_compiler::air::AirStmt::BumpAlloc {
                        persistent: true,
                        ..
                    }
                )
            })
        })
    });
    assert!(
        !has_persistent,
        "a state-free module must emit no persistent allocations"
    );
}

#[test]
fn state_free_map_tool_compiles_deterministically() {
    let a = compile_tool(STATE_FREE_MAP_TOOL).expect("compile 1");
    let b = compile_tool(STATE_FREE_MAP_TOOL).expect("compile 2");
    assert_eq!(
        a.wasm, b.wasm,
        "state-free map lowering must be byte-identical across compiles (I6)"
    );
}

const STATE_MAP_ACTOR: &str = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Store>(fuel); w.send(Put(1, 10)); return 0; }
}
actor Store {
    state { mut m: Map<i64, i64> }
    init(f: Fuel) { let tmp: Map<i64, i64> = Map::new(); m = tmp; }
    on Put(k: i64, v: i64) { let n: i64 = m.insert(k, v); }
}
"#;

#[test]
fn state_map_actor_compiles_deterministically() {
    let a = compile_module(STATE_MAP_ACTOR).expect("compile 1");
    let b = compile_module(STATE_MAP_ACTOR).expect("compile 2");
    assert_eq!(
        a.wasm_inner, b.wasm_inner,
        "state-map lowering must be byte-identical across compiles (I6)"
    );
}

#[test]
fn state_map_actor_emits_the_persistent_channel() {
    // The positive control for the invariant above: this module DOES route
    // interior allocations persistently, so the flag is not vacuous.
    let compiled = compile_module(STATE_MAP_ACTOR).expect("state map actor compiles");
    let persistent_instances: Vec<&str> = compiled
        .air
        .functions
        .iter()
        .filter(|f| {
            f.blocks.iter().any(|b| {
                b.stmts.iter().any(|s| {
                    matches!(
                        s,
                        sigil_compiler::air::AirStmt::IntrinsicAlloc {
                            persistent: true,
                            ..
                        } | sigil_compiler::air::AirStmt::BumpAlloc {
                            persistent: true,
                            ..
                        }
                    )
                })
            })
        })
        .map(|f| f.name.as_str())
        .collect();
    assert!(
        !persistent_instances.is_empty(),
        "a `mut Map` state actor must route interior allocations persistently"
    );
    assert!(
        persistent_instances
            .iter()
            .all(|name| name.ends_with("$state")),
        "only state-backed instances may allocate persistently; got {persistent_instances:?}"
    );
}
