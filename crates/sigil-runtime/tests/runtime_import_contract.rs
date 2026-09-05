//! Totality and fail-closed checks for the Wasm host-import boundary.

use std::collections::BTreeSet;

use sigil_abi::RuntimeTypeSpec;
use sigil_runtime::grants::IoGrants;
use sigil_runtime::{
    RuntimeActorSpec, RuntimeHandlerSpec, RuntimeHost, RuntimeImportSpec, RuntimeModuleSpec,
};

const EPHEMERAL_SOURCE: &str = include_str!("../src/ephemeral.rs");
const RUNTIME_SOURCE: &str = include_str!("../src/runtime.rs");

#[derive(Clone, Copy)]
struct ImportContract {
    module: &'static str,
    name: &'static str,
    params: &'static str,
    result: &'static str,
}

const ACTOR_IMPORTS: &[ImportContract] = &[
    ImportContract {
        module: "sigil",
        name: "fuel_decrement",
        params: "i32",
        result: "",
    },
    ImportContract {
        module: "sigil",
        name: "send",
        params: "i32 i32 i32 i32",
        result: "",
    },
    ImportContract {
        module: "sigil",
        name: "ask",
        params: "i32 i32 i32 i32 i64",
        result: "i64",
    },
    ImportContract {
        module: "sigil",
        name: "spawn",
        params: "i32 i32 i32 i32 i32",
        result: "i32",
    },
    ImportContract {
        module: "sigil",
        name: "alloc",
        params: "i32",
        result: "i32",
    },
    ImportContract {
        module: "sigil",
        name: "alloc_persistent",
        params: "i32",
        result: "i32",
    },
    ImportContract {
        module: "sigil",
        name: "cap_restrict",
        params: "i32 i32",
        result: "i32",
    },
    ImportContract {
        module: "sigil",
        name: "cap_split",
        params: "i32 i64",
        result: "i32",
    },
    ImportContract {
        module: "sigil",
        name: "cap_mint",
        params: "",
        result: "i32",
    },
];

const FORGE_SIGIL_IMPORTS: &[ImportContract] = &[
    ImportContract {
        module: "sigil",
        name: "fuel_decrement",
        params: "i32",
        result: "",
    },
    ImportContract {
        module: "sigil",
        name: "fuel_exhausted",
        params: "",
        result: "",
    },
    ImportContract {
        module: "sigil",
        name: "alloc",
        params: "i32",
        result: "i32",
    },
    ImportContract {
        module: "sigil",
        name: "send",
        params: "i32 i32 i32 i32",
        result: "",
    },
    ImportContract {
        module: "sigil",
        name: "ask",
        params: "i32 i32 i32 i32 i64",
        result: "i64",
    },
    ImportContract {
        module: "sigil",
        name: "spawn",
        params: "i32 i32 i32 i32 i32",
        result: "i32",
    },
    ImportContract {
        module: "sigil",
        name: "cap_restrict",
        params: "i32 i32",
        result: "i32",
    },
    ImportContract {
        module: "sigil",
        name: "cap_split",
        params: "i32 i64",
        result: "i32",
    },
    ImportContract {
        module: "sigil",
        name: "cap_mint",
        params: "",
        result: "i32",
    },
];

const FORGE_FFI_IMPORTS: &[ImportContract] = &[
    ImportContract {
        module: "ffi",
        name: "http_get",
        params: "i32 i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "http_post",
        params: "i32 i32 i32 i32",
        result: "i64",
    },
    // Outbound POST with caller-supplied request headers (agent-framework
    // arc): url ptr/len, body ptr/len, header-blob ptr/len.
    ImportContract {
        module: "ffi",
        name: "http_post_hdrs",
        params: "i32 i32 i32 i32 i32 i32",
        result: "i64",
    },
    // Same shape, but the header blob may carry `{{secret:NAME}}` placeholders
    // the host substitutes from a `SecretGrant` before sending.
    ImportContract {
        module: "ffi",
        name: "http_post_secret",
        params: "i32 i32 i32 i32 i32 i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "fs_read",
        params: "i32 i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "fs_list",
        params: "i32 i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "fs_write",
        params: "i32 i32 i32 i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "crypto_sha256",
        params: "i32 i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "crypto_sha512",
        params: "i32 i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "time_now",
        params: "",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "random_bytes",
        params: "i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "kv_get",
        params: "i32 i32 i32 i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "kv_put",
        params: "i32 i32 i32 i32 i32 i32",
        result: "i64",
    },
    ImportContract {
        module: "ffi",
        name: "kv_delete",
        params: "i32 i32 i32 i32",
        result: "i64",
    },
];

const SOLVER_FFI_IMPORT: ImportContract = ImportContract {
    module: "ffi",
    name: "z3_check",
    params: "i32 i32",
    result: "i64",
};

fn region<'a>(src: &'a str, start: &str, end: &str) -> &'a str {
    let (_, tail) = src
        .split_once(start)
        .unwrap_or_else(|| panic!("source contract lost start marker {start:?}"));
    tail.split_once(end)
        .unwrap_or_else(|| panic!("source contract lost end marker {end:?}"))
        .0
}

fn literal_func_wraps(src: &str) -> BTreeSet<(String, String)> {
    src.split(".func_wrap(")
        .skip(1)
        .map(|tail| {
            let mut quoted = tail.split('"');
            let _ = quoted.next();
            let module = quoted.next().expect("func_wrap module must be a literal");
            let _ = quoted.next();
            let name = quoted.next().expect("func_wrap name must be a literal");
            (module.to_owned(), name.to_owned())
        })
        .collect()
}

fn names(contracts: &[ImportContract]) -> BTreeSet<(String, String)> {
    contracts
        .iter()
        .map(|contract| (contract.module.to_owned(), contract.name.to_owned()))
        .collect()
}

fn import_declarations(contracts: &[ImportContract]) -> String {
    contracts
        .iter()
        .enumerate()
        .map(|(index, contract)| {
            let result = if contract.result.is_empty() {
                String::new()
            } else {
                format!("(result {})", contract.result)
            };
            format!(
                "(import \"{}\" \"{}\" (func $i{index} (param {}) {result}))",
                contract.module, contract.name, contract.params
            )
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn forge_wat(contracts: &[ImportContract]) -> Vec<u8> {
    wat::parse_str(format!(
        r#"(module
  {}
  (memory (export "memory") 1)
  (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
  (func (export "tool__tool_main") (param i64 i64) (result i64) (i64.const 0)))"#,
        import_declarations(contracts)
    ))
    .expect("forge import-contract WAT parses")
}

fn actor_wat(contracts: &[ImportContract]) -> Vec<u8> {
    wat::parse_str(format!(
        r#"(module
  {}
  (memory (export "memory") 1)
  (func (export "Main__Start") (param i32) (result i64) (i64.const 0)))"#,
        import_declarations(contracts)
    ))
    .expect("actor import-contract WAT parses")
}

fn actor_spec() -> RuntimeModuleSpec {
    RuntimeModuleSpec {
        module_name: "import_contract".to_owned(),
        fuel_budget: 4096,
        imports: RuntimeImportSpec::phase_one(),
        actors: vec![RuntimeActorSpec {
            name: "Main".to_owned(),
            actor_type_id: 0,
            is_entry: true,
            init_export: None,
            init_params: vec![],
            handlers: vec![RuntimeHandlerSpec {
                name: "Start".to_owned(),
                handler_id: 0,
                export_name: "Main__Start".to_owned(),
                params: vec![],
                ret: RuntimeTypeSpec::I64,
            }],
            state_layout: vec![],
            state_size: 0,
            init_replay_safe: false,
        }],
    }
}

#[test]
fn host_import_manifests_are_total_over_linker_registrations() {
    let sigil_region = region(
        EPHEMERAL_SOURCE,
        "fn link_sigil_imports(",
        "fn link_ffi_imports(",
    );
    assert_eq!(
        literal_func_wraps(sigil_region),
        names(FORGE_SIGIL_IMPORTS),
        "every forge `sigil` registration must be classified"
    );

    let ffi_region = region(
        EPHEMERAL_SOURCE,
        "fn link_ffi_imports(",
        "const MAX_RANDOM_BYTES",
    );
    let mut expected_ffi = names(FORGE_FFI_IMPORTS);
    expected_ffi.insert((
        SOLVER_FFI_IMPORT.module.to_owned(),
        SOLVER_FFI_IMPORT.name.to_owned(),
    ));
    assert_eq!(
        literal_func_wraps(ffi_region),
        expected_ffi,
        "every forge `ffi` registration, including feature-gated ones, must be classified"
    );

    let actor_region = region(
        RUNTIME_SOURCE,
        "fn instantiate_runtime(",
        "fn collect_runtime_exports(",
    );
    assert_eq!(
        actor_region.matches(".func_wrap(").count(),
        ACTOR_IMPORTS.len(),
        "every actor linker registration must have one manifest row"
    );
    let fields: BTreeSet<&str> = actor_region
        .match_indices("&module_spec.imports.")
        .map(|(offset, marker)| {
            actor_region[offset + marker.len()..]
                .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .next()
                .unwrap_or_default()
        })
        .filter(|field| *field != "module")
        .collect();
    let expected_fields: BTreeSet<&str> = ACTOR_IMPORTS.iter().map(|row| row.name).collect();
    assert_eq!(
        fields, expected_fields,
        "actor import fields drifted from the manifest"
    );
}

#[test]
fn declared_host_imports_really_link_and_unknown_imports_fail_closed() {
    sigil_runtime::execute_ephemeral(
        &forge_wat(FORGE_SIGIL_IMPORTS),
        b"",
        4096,
        &IoGrants::none(),
    )
    .expect("all declared forge `sigil` imports must link");
    sigil_runtime::execute_ephemeral(&forge_wat(FORGE_FFI_IMPORTS), b"", 4096, &IoGrants::none())
        .expect("all unconditional forge `ffi` imports must link");

    let spec = actor_spec();
    RuntimeHost::new(spec.fuel_budget)
        .bootstrap(&spec, &actor_wat(ACTOR_IMPORTS))
        .expect("all declared actor imports must link");

    let unknown = [ImportContract {
        module: "sigil",
        name: "unclassified_import",
        params: "",
        result: "",
    }];
    assert!(
        sigil_runtime::execute_ephemeral(&forge_wat(&unknown), b"", 4096, &IoGrants::none(),)
            .is_err(),
        "an unknown forge import must fail at instantiation"
    );
    assert!(
        RuntimeHost::new(spec.fuel_budget)
            .bootstrap(&spec, &actor_wat(&unknown))
            .is_err(),
        "an unknown actor import must fail at instantiation"
    );

    let actor_only = [*ACTOR_IMPORTS
        .iter()
        .find(|row| row.name == "alloc_persistent")
        .expect("actor manifest has alloc_persistent")];
    assert!(
        sigil_runtime::execute_ephemeral(&forge_wat(&actor_only), b"", 4096, &IoGrants::none(),)
            .is_err(),
        "an actor-only import must not silently appear in the forge"
    );
}
