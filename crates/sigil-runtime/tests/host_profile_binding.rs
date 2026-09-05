//! Runtime-bound contract witnesses. These are not CSIR/Public-theorem claims:
//! the callback bodies implement the declared isolation by construction here.

use sigil_abi::host_contract::{
    HOST_PROFILE_SECTION, HostAccessMode, HostContractError, HostDomain, HostDomainAccess,
    HostDomainKind, HostDomainScope, HostOperationContract, HostProfileRequirement,
    HostValueContract, HostValueType, OccurrenceVisibility, SecurityLabel,
};
use sigil_runtime::host_contract::{HostBindingError, HostBindingsBuilder, InstalledHostBindings};
use sigil_runtime::{
    IoGrants, RuntimeHost, RuntimeImportSpec, RuntimeModuleSpec, ephemeral_host_profile,
    execute_ephemeral, execute_ephemeral_with_memory_budget,
};
use wasmtime::{Caller, Engine, Store};

#[derive(Default)]
struct HostState {
    public: i64,
    private: i64,
}

fn domain(name: &str, label: SecurityLabel) -> HostDomain {
    HostDomain {
        name: name.into(),
        kind: HostDomainKind::InputStream,
        scope: HostDomainScope::Shared,
        label,
    }
}

fn next_contract(
    name: &str,
    occurrence: OccurrenceVisibility,
    state: &str,
) -> HostOperationContract {
    HostOperationContract {
        module: "host".into(),
        name: name.into(),
        occurrence,
        params: vec![],
        results: vec![HostValueContract {
            ty: HostValueType::I64,
            label: occurrence.label(),
        }],
        domains: vec![HostDomainAccess {
            domain: state.into(),
            mode: HostAccessMode::ReadWrite,
        }],
    }
}

fn installed(
    engine: &Engine,
    store: &mut Store<HostState>,
    revision: u64,
) -> InstalledHostBindings<HostState> {
    HostBindingsBuilder::new(
        engine,
        "isolated-test-host".into(),
        revision,
        vec![
            domain("public", SecurityLabel::Public),
            domain("private", SecurityLabel::Secret),
        ],
    )
    .define(
        next_contract("public_next", OccurrenceVisibility::Public, "public"),
        |mut caller: Caller<'_, HostState>| -> i64 {
            let result = caller.data().public;
            caller.data_mut().public += 1;
            result
        },
    )
    .unwrap()
    .define(
        next_contract("private_next", OccurrenceVisibility::Secret, "private"),
        |mut caller: Caller<'_, HostState>| -> i64 {
            let result = caller.data().private;
            caller.data_mut().private += 1;
            result
        },
    )
    .unwrap()
    .finish(store)
    .unwrap()
}

fn append_uleb(bytes: &mut Vec<u8>, mut value: usize) {
    loop {
        let byte = (value & 0x7f) as u8;
        value >>= 7;
        bytes.push(byte | if value == 0 { 0 } else { 0x80 });
        if value == 0 {
            break;
        }
    }
}

fn append_custom(wasm: &mut Vec<u8>, name: &str, payload: &[u8]) {
    let mut content = Vec::new();
    append_uleb(&mut content, name.len());
    content.extend_from_slice(name.as_bytes());
    content.extend_from_slice(payload);
    wasm.push(0);
    append_uleb(wasm, content.len());
    wasm.extend_from_slice(&content);
}

fn bind(wasm: &mut Vec<u8>, bindings: &InstalledHostBindings<HostState>) {
    append_custom(
        wasm,
        HOST_PROFILE_SECTION,
        &HostProfileRequirement {
            fingerprint: bindings.profile().fingerprint(),
        }
        .encode(),
    );
}

fn start_module() -> Vec<u8> {
    wat::parse_str(
        r#"(module
      (import "host" "public_next" (func $next (result i64)))
      (func $start call $next drop)
      (start $start))"#,
    )
    .unwrap()
}

#[test]
fn matching_installed_profile_executes_real_start_callback() {
    let engine = Engine::default();
    let mut store = Store::new(&engine, HostState::default());
    let bindings = installed(&engine, &mut store, 1);
    let mut wasm = start_module();
    bind(&mut wasm, &bindings);
    bindings.instantiate(&mut store, &wasm).unwrap();
    assert_eq!(store.data().public, 1);
}

#[test]
fn missing_stale_changed_duplicate_or_unknown_profile_never_runs_start() {
    let engine = Engine::default();
    let mut store = Store::new(&engine, HostState::default());
    let bindings = installed(&engine, &mut store, 1);
    let newer = installed(&engine, &mut store, 2);
    let mut stale = start_module();
    bind(&mut stale, &bindings);
    assert!(matches!(
        newer.instantiate(&mut store, &stale),
        Err(HostBindingError::Contract(
            HostContractError::ProfileMismatch
        ))
    ));
    assert_eq!(store.data().public, 0);
    assert!(matches!(
        bindings.instantiate(&mut store, &start_module()),
        Err(HostBindingError::MissingProfile)
    ));
    let mut changed = stale.clone();
    *changed.last_mut().unwrap() ^= 1;
    assert!(matches!(
        bindings.instantiate(&mut store, &changed),
        Err(HostBindingError::Contract(
            HostContractError::ProfileMismatch
        ))
    ));
    let mut duplicate = stale.clone();
    bind(&mut duplicate, &bindings);
    assert!(matches!(
        bindings.instantiate(&mut store, &duplicate),
        Err(HostBindingError::DuplicateProfile)
    ));
    let mut unknown = start_module();
    append_custom(&mut unknown, "sigil.host-profile.v2", &[0; 36]);
    assert!(matches!(
        bindings.instantiate(&mut store, &unknown),
        Err(HostBindingError::UnknownProfileSection)
    ));
    assert_eq!(store.data().public, 0);
}

#[test]
fn malformed_requirement_cannot_be_ignored_before_start() {
    let engine = Engine::default();
    let mut store = Store::new(&engine, HostState::default());
    let bindings = installed(&engine, &mut store, 1);
    let data = HostProfileRequirement {
        fingerprint: bindings.profile().fingerprint(),
    }
    .encode();
    for length in 0..data.len() {
        let mut wasm = start_module();
        append_custom(&mut wasm, HOST_PROFILE_SECTION, &data[..length]);
        assert!(
            bindings.instantiate(&mut store, &wasm).is_err(),
            "accepted truncated requirement length {length}"
        );
    }
    let mut version = data;
    version[..4].copy_from_slice(&2_u32.to_le_bytes());
    let mut wasm = start_module();
    append_custom(&mut wasm, HOST_PROFILE_SECTION, &version);
    assert!(matches!(
        bindings.instantiate(&mut store, &wasm),
        Err(HostBindingError::Contract(
            HostContractError::UnsupportedVersion(2)
        ))
    ));
    assert_eq!(store.data().public, 0);
}

#[test]
fn declared_signature_must_match_the_real_callback() {
    let engine = Engine::default();
    let mut store = Store::new(&engine, HostState::default());
    let mut contract = next_contract("public_next", OccurrenceVisibility::Public, "public");
    contract.results[0].ty = HostValueType::I32;
    let candidate = HostBindingsBuilder::new(
        &engine,
        "test".into(),
        1,
        vec![domain("public", SecurityLabel::Public)],
    )
    .define(contract, |_: Caller<'_, HostState>| -> i64 { 0 })
    .unwrap()
    .finish(&mut store);
    assert!(matches!(
        candidate,
        Err(HostBindingError::Contract(
            HostContractError::SignatureMismatch { .. }
        ))
    ));
}

#[test]
fn guest_signature_mismatch_or_unknown_import_is_rejected_before_start() {
    let engine = Engine::default();
    let mut store = Store::new(&engine, HostState::default());
    let bindings = installed(&engine, &mut store, 1);
    for text in [
        r#"(module (import "host" "public_next" (func $next (result i32))) (func $start call $next drop) (start $start))"#,
        r#"(module (import "other" "public_next" (func $next (result i64))) (func $start call $next drop) (start $start))"#,
        r#"(module (import "host" "unknown" (func $next (result i64))) (func $start call $next drop) (start $start))"#,
    ] {
        let mut wasm = wat::parse_str(text).unwrap();
        bind(&mut wasm, &bindings);
        assert!(bindings.instantiate(&mut store, &wasm).is_err());
        assert_eq!(store.data().public, 0);
    }
}

#[test]
fn private_calls_do_not_shift_public_results_in_the_isolated_host_witness() {
    let engine = Engine::default();
    let mut left = Store::new(&engine, HostState::default());
    let mut right = Store::new(&engine, HostState::default());
    let bindings = installed(&engine, &mut left, 1);
    let mut wasm = wat::parse_str(
        r#"(module
      (import "host" "public_next" (func $public (result i64)))
      (import "host" "private_next" (func $private (result i64)))
      (func (export "run") (param $count i32) (result i64)
        (block $done (loop $again
          local.get $count i32.eqz br_if $done
          call $private drop
          local.get $count i32.const 1 i32.sub local.set $count
          br $again))
        call $public))"#,
    )
    .unwrap();
    bind(&mut wasm, &bindings);
    let li = bindings.instantiate(&mut left, &wasm).unwrap();
    let ri = bindings.instantiate(&mut right, &wasm).unwrap();
    let lrun = li.get_typed_func::<i32, i64>(&mut left, "run").unwrap();
    let rrun = ri.get_typed_func::<i32, i64>(&mut right, "run").unwrap();
    assert_eq!(
        lrun.call(&mut left, 0).unwrap(),
        rrun.call(&mut right, 7).unwrap()
    );
    assert_eq!(left.data().public, right.data().public);
    assert_eq!(left.data().private, 0);
    assert_eq!(right.data().private, 7);
}

#[test]
fn foreign_engine_returns_an_error_not_a_panic() {
    let engine = Engine::default();
    let foreign = Engine::default();
    let mut store = Store::new(&engine, HostState::default());
    let mut foreign_store = Store::new(&foreign, HostState::default());
    let bindings = installed(&engine, &mut store, 1);
    let mut wasm = start_module();
    bind(&mut wasm, &bindings);
    assert!(matches!(
        bindings.instantiate(&mut foreign_store, &wasm),
        Err(HostBindingError::EngineMismatch)
    ));
    assert!(matches!(
        HostBindingsBuilder::new(&engine, "test".into(), 1, vec![]).finish(&mut foreign_store),
        Err(HostBindingError::EngineMismatch)
    ));
}

fn empty_spec() -> RuntimeModuleSpec {
    RuntimeModuleSpec {
        module_name: "test".into(),
        fuel_budget: 1000,
        imports: RuntimeImportSpec::phase_one(),
        actors: vec![],
    }
}

#[test]
fn legacy_actor_and_ephemeral_entry_points_do_not_ignore_host_requirements() {
    let base = wat::parse_str(
        r#"(module (memory (export "memory") 1)
      (global (export "BUMP_PTR") (mut i32) (i32.const 16))
      (func (export "tool_main") (param i32 i32) (result i64) i64.const 0))"#,
    )
    .unwrap();
    assert!(
        RuntimeHost::new(1000)
            .bootstrap(&empty_spec(), &base)
            .is_ok()
    );
    assert!(execute_ephemeral(&base, b"", 1000, &IoGrants::none()).is_ok());

    // A requirement neither entry point implements: the actor host declares no profile at
    // all, and the ephemeral host's declared profile has a different fingerprint.
    let mut foreign = base.clone();
    append_custom(
        &mut foreign,
        HOST_PROFILE_SECTION,
        &HostProfileRequirement {
            fingerprint: [0; 32],
        }
        .encode(),
    );
    let actor = RuntimeHost::new(1000)
        .bootstrap(&empty_spec(), &foreign)
        .unwrap_err()
        .to_string();
    let ephemeral = execute_ephemeral(&foreign, b"", 1000, &IoGrants::none())
        .unwrap_err()
        .to_string();
    assert!(
        actor.contains("requires contract-bound instantiation"),
        "{actor}"
    );
    assert!(
        ephemeral.contains("required host profile differs from installed profile"),
        "{ephemeral}"
    );

    // The ephemeral host's own fingerprint is the one requirement it satisfies. The actor
    // host declares nothing, so it keeps refusing every requirement, this one included.
    let mut bound = base;
    append_custom(
        &mut bound,
        HOST_PROFILE_SECTION,
        &HostProfileRequirement {
            fingerprint: ephemeral_host_profile().fingerprint(),
        }
        .encode(),
    );
    let actor = RuntimeHost::new(1000)
        .bootstrap(&empty_spec(), &bound)
        .unwrap_err()
        .to_string();
    assert!(
        actor.contains("requires contract-bound instantiation"),
        "{actor}"
    );
    execute_ephemeral(&bound, b"", 1000, &IoGrants::none())
        .expect("a module bound to the ephemeral host's declared profile runs under it");
}

#[test]
fn legacy_ephemeral_preserves_profile_free_wat_input() {
    let text = br#";; The legacy Module::new path also accepts text, not only binaries.
      (module (memory (export "memory") 1)
        (global (export "BUMP_PTR") (mut i32) (i32.const 16))
        (func (export "tool_main") (param i32 i32) (result i64) i64.const 0))"#;
    // Establish that the same text is a valid input to the preexisting loader.
    wasmtime::Module::new(&Engine::default(), text).unwrap();
    execute_ephemeral(text, b"", 1000, &IoGrants::none()).unwrap();
    execute_ephemeral_with_memory_budget(text, b"", 1000, 2 * 1024 * 1024, &IoGrants::none())
        .unwrap();
    // The actor API has always required binary input; do not widen it incidentally.
    assert!(
        RuntimeHost::new(1000)
            .bootstrap(&empty_spec(), text)
            .is_err()
    );
}

#[test]
fn text_encoded_host_requirements_are_checked_before_start() {
    let module_text = |fingerprint: [u8; 32]| {
        let payload: String = HostProfileRequirement { fingerprint }
            .encode()
            .iter()
            .map(|byte| format!("\\{byte:02x}"))
            .collect();
        format!(
            r#"(; Text normalization must not skip reserved custom sections. ;)
        (module (@custom "sigil.host-profile" "{payload}")
          (func $start unreachable) (start $start)
          (memory (export "memory") 1)
          (global (export "BUMP_PTR") (mut i32) (i32.const 16))
          (func (export "tool_main") (param i32 i32) (result i64) i64.const 0))"#
        )
    };
    let foreign = module_text([0; 32]);
    wasmtime::Module::new(&Engine::default(), foreign.as_bytes()).unwrap();
    for error in [
        execute_ephemeral(foreign.as_bytes(), b"", 1000, &IoGrants::none()).unwrap_err(),
        execute_ephemeral_with_memory_budget(
            foreign.as_bytes(),
            b"",
            1000,
            2 * 1024 * 1024,
            &IoGrants::none(),
        )
        .unwrap_err(),
    ] {
        // The refusal names the profile, so the check ran before `start` could trap.
        assert!(
            error
                .to_string()
                .contains("required host profile differs from installed profile"),
            "{error}"
        );
    }
    // The section's content is read, not only its presence: the ephemeral host's own
    // fingerprint is accepted, and the module then reaches its trapping `start`.
    let bound = module_text(ephemeral_host_profile().fingerprint());
    let error = execute_ephemeral(bound.as_bytes(), b"", 1000, &IoGrants::none()).unwrap_err();
    assert!(!error.to_string().contains("host profile"), "{error}");
}
