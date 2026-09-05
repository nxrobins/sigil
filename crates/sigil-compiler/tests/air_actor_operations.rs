//! WHY THIS TEST EXISTS. The actor-boundary opcode in v8 erases the distinction
//! between send, ask, spawn, serialization, and deserialization. Pending-v9 AIR
//! metadata preserves constructor identity, not an inferred security verdict.
//! These tests pin its numeric mapping and prove that v8, runtime Wasm, and AIR
//! snapshots still ignore the new side table. No v9 wire emission is asserted.

use std::collections::{BTreeMap, BTreeSet};

use sigil_compiler::air::{
    self, ActorTypeId, AirActorOperation, AirFunction, AirProgram, AirStmt, AirSupervisionStrategy,
    AirValue, HandlerId, VarId,
};
use sigil_compiler::diagnostics::codes;
use sigil_compiler::{CompileOptions, compile_named_module, formal, fuel, memory, wasm};

const AIR_SOURCE: &str = include_str!("../src/air.rs");
const SOURCE: &str = r#"
module actor_metadata;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>) -> i64 {
        worker.send(Ping());
        let child = spawn::<Worker>(fuel);
        let response = worker.ask(GetCount(), timeout: 5);
        return response;
    }
}
actor Worker {
    init(fuel: Fuel) {}
    on Ping() {}
    on GetCount() -> i64 { return 1; }
}
"#;

fn actor_statements(payload_count: usize) -> [AirStmt; 5] {
    let payload = vec![VarId(0); payload_count];
    [
        AirStmt::MessageSend {
            target: VarId(0),
            msg: VarId(0),
            actor_type: ActorTypeId(1),
            handler: HandlerId(1),
            payload_buf: VarId(0),
            payload_len: VarId(0),
        },
        AirStmt::MessageAsk {
            dst: VarId(0),
            target: VarId(0),
            msg: VarId(0),
            actor_type: ActorTypeId(1),
            handler: HandlerId(1),
            payload_buf: VarId(0),
            payload_len: VarId(0),
            timeout: VarId(0),
        },
        AirStmt::SpawnActor {
            dst: VarId(0),
            actor_type: ActorTypeId(1),
            caps: payload.clone(),
            fuel_cap: VarId(0),
            supervision: AirSupervisionStrategy::Stop,
        },
        AirStmt::SerializeMessage {
            msg: VarId(0),
            args: payload,
            dst_buf: VarId(0),
            dst_len: VarId(0),
        },
        AirStmt::DeserializeMessage {
            src_buf: VarId(0),
            src_len: VarId(0),
            dst: VarId(0),
        },
    ]
}

#[test]
fn actor_constructor_codes_are_stable_and_independent_of_payload_arity() {
    let expected = [
        (AirActorOperation::Send, 1),
        (AirActorOperation::Ask, 2),
        (AirActorOperation::Spawn, 3),
        (AirActorOperation::Serialize, 4),
        (AirActorOperation::Deserialize, 5),
    ];
    for payload_count in 0..=8 {
        for (statement, (operation, code)) in actor_statements(payload_count).iter().zip(expected) {
            assert_eq!(statement.actor_operation(), Some(operation));
            assert_eq!(operation as u32, code);
        }
    }
    // A call with the same payload shape remains a call, not an actor action.
    assert_eq!(
        AirStmt::ExternCall {
            dst: Some(VarId(0)),
            extern_name: "send".into(),
            args: vec![VarId(0); 4],
        }
        .actor_operation(),
        None,
    );
}

fn classifier_inventory_matches(source: &str) -> bool {
    let Some((_, enum_tail)) = source.split_once("pub enum AirStmt {") else {
        return false;
    };
    let Some((enum_body, _)) = enum_tail.split_once("\n}") else {
        return false;
    };
    let Some((_, method_tail)) =
        source.split_once("pub const fn actor_operation(&self) -> Option<AirActorOperation> {")
    else {
        return false;
    };
    let Some((method_body, _)) = method_tail.split_once("\n    }\n}") else {
        return false;
    };
    if method_body.contains("_ =>") {
        return false;
    }
    let constructors: BTreeSet<_> = enum_body
        .lines()
        .filter_map(|line| {
            let name = line.strip_prefix("    ")?.strip_suffix(" {")?;
            name.chars()
                .all(|c| c.is_ascii_alphanumeric())
                .then_some(name.to_owned())
        })
        .collect();
    let classified: BTreeSet<_> = method_body
        .split("Self::")
        .skip(1)
        .map(|tail| {
            tail.chars()
                .take_while(|c| c.is_ascii_alphanumeric())
                .collect::<String>()
        })
        .collect();
    !constructors.is_empty() && constructors == classified
}

#[test]
fn every_air_constructor_has_an_explicit_actor_classification() {
    assert!(classifier_inventory_matches(AIR_SOURCE));
    assert!(!classifier_inventory_matches(""));
    // SC-P4: prove the inventory detects a newly added constructor, a missing
    // classification arm, and a wildcard that would hide future actor variants.
    let added = AIR_SOURCE.replacen(
        "pub enum AirStmt {",
        "pub enum AirStmt {\n    PlantedActor {",
        1,
    );
    assert!(!classifier_inventory_matches(&added));
    let missing = AIR_SOURCE.replace("| Self::RegionEnd { .. }", "");
    assert!(!classifier_inventory_matches(&missing));
    let wildcard = AIR_SOURCE.replace(
        "Self::MessageSend { .. } =>",
        "_ => None,\n            Self::MessageSend { .. } =>",
    );
    assert!(!classifier_inventory_matches(&wildcard));
}

fn records_match_statements(function: &AirFunction) -> bool {
    let mut expected = BTreeMap::new();
    for block in &function.blocks {
        for (index, statement) in block.stmts.iter().enumerate() {
            // Independent expected mapping: do not call the classifier being
            // checked, or a wrong classifier and recorder could agree vacuously.
            let operation = match statement {
                AirStmt::MessageSend { .. } => Some(AirActorOperation::Send),
                AirStmt::MessageAsk { .. } => Some(AirActorOperation::Ask),
                AirStmt::SpawnActor { .. } => Some(AirActorOperation::Spawn),
                AirStmt::SerializeMessage { .. } => Some(AirActorOperation::Serialize),
                AirStmt::DeserializeMessage { .. } => Some(AirActorOperation::Deserialize),
                _ => None,
            };
            if let Some(operation) = operation {
                expected.insert(
                    (
                        block.id,
                        u32::try_from(index).expect("fixture index fits u32"),
                    ),
                    operation,
                );
            }
        }
    }
    expected == function.security.actor_operations
}

#[test]
fn lowering_records_every_actor_site_at_the_formal_gate_cut() {
    let compilation = compile_named_module("actor_metadata.sigil", SOURCE)
        .expect("the existing send/ask/spawn fixture compiles through v8");
    // Compilation.air is already rewritten by memory/fuel passes. Re-lower the
    // retained typed program to inspect exactly the raw AIR formal verification sees.
    let raw = air::lower(&compilation.typed);
    assert!(raw.functions.iter().all(records_match_statements));
    let operations: Vec<_> = raw
        .functions
        .iter()
        .flat_map(|f| f.security.actor_operations.values().copied())
        .collect();
    assert_eq!(
        operations,
        vec![
            AirActorOperation::Serialize,
            AirActorOperation::Send,
            AirActorOperation::Spawn,
            AirActorOperation::Serialize,
            AirActorOperation::Ask
        ]
    );
    assert_eq!(raw, air::lower(&compilation.typed));

    let original = raw
        .functions
        .iter()
        .find(|f| !f.security.actor_operations.is_empty())
        .expect("the fixture has actor-operation records");
    let mut missing = original.clone();
    missing.security.actor_operations.pop_first();
    assert!(!records_match_statements(&missing));
    let mut changed = original.clone();
    *changed
        .security
        .actor_operations
        .values_mut()
        .next()
        .expect("the fixture has an actor-operation record") = AirActorOperation::Deserialize;
    assert!(!records_match_statements(&changed));
}

fn runtime_bytes(raw: AirProgram) -> (Vec<u8>, Option<Vec<u8>>) {
    let (air, _) = memory::lower(raw);
    let (air, _) = fuel::insert(air);
    let output = wasm::emit(&air);
    (output.inner, output.outer)
}

#[test]
fn actor_metadata_does_not_change_v8_evidence_runtime_bytes_or_air_snapshots() {
    let compilation = compile_named_module("actor_metadata.sigil", SOURCE)
        .expect("the existing actor fixture compiles through v8");
    let raw = air::lower(&compilation.typed);
    let resolved = sigil_compiler::name_resolution::resolve(&compilation.ast)
        .expect("the compiled fixture has valid name resolution");
    let (_, authority, _) =
        sigil_compiler::type_check::check_with_warnings(&resolved, &CompileOptions::default())
            .expect("the compiled fixture has valid authority declarations");
    let report = formal::verify(&compilation.typed, &raw, &authority)
        .expect("re-lowered raw AIR passes the unchanged v8 verifier");
    assert_eq!(report, compilation.formal_security_report);
    let different_source = compile_named_module(
        "actor_metadata.sigil",
        SOURCE.replace("return 1;", "return 2;"),
    )
    .expect("a different worker return value is a valid actor program");
    assert_ne!(
        report.csir_fingerprint, different_source.formal_security_report.csir_fingerprint,
        "the v8 evidence comparator must detect a real semantic literal change"
    );
    let debug = format!("{raw:#?}");
    let bytes = runtime_bytes(raw.clone());
    assert_eq!(bytes, (compilation.wasm_inner, compilation.wasm_outer));

    for remove in [false, true] {
        let mut changed = raw.clone();
        for function in &mut changed.functions {
            if remove {
                function.security.actor_operations.clear();
            } else {
                for operation in function.security.actor_operations.values_mut() {
                    *operation = AirActorOperation::Deserialize;
                }
            }
        }
        assert_eq!(format!("{changed:#?}"), debug);
        assert_eq!(runtime_bytes(changed.clone()), bytes);
        // The AIR snapshot and the runtime bytes ignore the table; the production
        // gate does not. Its v9 projection refuses a record that disagrees with,
        // or is missing for, the actual AIR instruction (I013, fail closed)
        // instead of re-inferring the contract from the instruction.
        let diagnostics = formal::verify(&compilation.typed, &changed, &authority)
            .expect_err("the v9 projection must refuse actor metadata that disagrees with AIR");
        assert_eq!(diagnostics.len(), 1, "remove={remove}: {diagnostics:?}");
        assert_eq!(diagnostics[0].code(), codes::I013, "remove={remove}");
        assert!(
            diagnostics[0]
                .message()
                .contains("v9 actor metadata does not match the actual AIR instruction"),
            "remove={remove}: {}",
            diagnostics[0].message()
        );
    }

    // A real runtime instruction mutation proves the snapshot/byte comparators
    // distinguish program changes even though they ignore metadata-only changes.
    let mut changed = raw;
    let value = changed
        .functions
        .iter_mut()
        .flat_map(|f| &mut f.blocks)
        .flat_map(|b| &mut b.stmts)
        .find_map(|statement| match statement {
            AirStmt::Assign {
                val: AirValue::IntLit(value),
                ..
            } if *value == 1 => Some(value),
            _ => None,
        })
        .expect("the fixture's worker returns a literal one");
    *value = 2;
    assert_ne!(format!("{changed:#?}"), debug);
    assert_ne!(runtime_bytes(changed), bytes);
}
