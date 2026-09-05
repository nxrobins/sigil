//! WHY THIS TEST EXISTS. Compiler declarations must resolve the operation that
//! Wasm actually imports, without treating payload privacy as occurrence privacy
//! or treating configuration as host approval. Rejects have minimally different
//! accept twins; pinned bytes/fingerprints expose identity or encoding drift.

use std::sync::Arc;

use sigil_abi::host_contract::{
    HostContractError, HostContractProfile, HostOperationContract, HostProfileRequirement,
    HostValueContract, HostValueType, MAX_HOST_NAME_BYTES, OccurrenceVisibility, SecurityLabel,
};
use sigil_compiler::{CompilerContext, CompilerContextError};

const TOOL_SOURCE: &str =
    "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }";

fn project_sources() -> Vec<sigil_compiler::source::SourceFile> {
    vec![
        sigil_compiler::source::SourceFile::new("tool.sigil", TOOL_SOURCE),
        sigil_compiler::source::SourceFile::new(
            "helper.sigil",
            "module helper; pub fn value() -> i64 { return 1; }",
        ),
    ]
}

#[test]
fn default_context_preserves_all_compiler_entry_artifacts_and_reports() {
    use sigil_compiler::*;
    let context = CompilerContext::default();
    let options = CompileOptions::default();
    let compare = |legacy: Compilation, explicit: Compilation| {
        assert_eq!(legacy.wasm_inner, explicit.wasm_inner);
        assert_eq!(legacy.wasm_outer, explicit.wasm_outer);
        assert_eq!(legacy.capability_report, explicit.capability_report);
        assert_eq!(legacy.ownership_report, explicit.ownership_report);
        assert_eq!(
            legacy.formal_security_report,
            explicit.formal_security_report
        );
        assert_eq!(legacy.effects_required, explicit.effects_required);
        assert_eq!(legacy.module_names, explicit.module_names);
    };
    compare(
        compile_module(TOOL_SOURCE).expect("ordinary inline source compiles"),
        compile_module_with_context(TOOL_SOURCE, &context)
            .expect("default context preserves inline compilation"),
    );
    compare(
        compile_named_module_with_options("tool.sigil", TOOL_SOURCE, options.clone())
            .expect("ordinary named source compiles"),
        compile_named_module_with_context("tool.sigil", TOOL_SOURCE, options.clone(), &context)
            .expect("default context preserves named compilation"),
    );
    compare(
        compile_project(project_sources(), Some("tool"), options.clone())
            .expect("ordinary project compiles"),
        compile_project_with_context(project_sources(), Some("tool"), options.clone(), &context)
            .expect("default context preserves project compilation"),
    );
    compare(
        compile_library_project(project_sources(), options.clone())
            .expect("ordinary library compiles"),
        compile_library_project_with_context(project_sources(), options, &context)
            .expect("default context preserves library compilation"),
    );
    let legacy = compile_tool(TOOL_SOURCE).expect("ordinary tool compiles");
    for explicit in [
        compile_tool_with_context(TOOL_SOURCE, &context),
        compile_tool_with_limits_and_context(TOOL_SOURCE, &CompileLimits::default(), &context),
    ] {
        let explicit = explicit.expect("default context preserves tool compilation");
        assert_eq!(legacy.wasm, explicit.wasm);
        assert_eq!(legacy.wasm_inner, explicit.wasm_inner);
        assert_eq!(legacy.wasm_outer, explicit.wasm_outer);
        assert_eq!(legacy.fuel_budget, explicit.fuel_budget);
        assert_eq!(
            legacy.fuel_is_workload_ceiling,
            explicit.fuel_is_workload_ceiling
        );
        assert_eq!(legacy.function_count, explicit.function_count);
        assert_eq!(legacy.solver_verified, explicit.solver_verified);
        assert_eq!(
            legacy.formal_security_report,
            explicit.formal_security_report
        );
    }
}

#[test]
fn every_compiler_entry_routes_profiles_through_the_production_v9_gate() {
    use sigil_compiler::*;
    // An empty declaration set is still an explicit profile requirement. It must reach both the
    // v9 formal envelope and Wasm binding even when source makes no extern calls.
    let context = CompilerContext::with_host_profile(profile(vec![]));
    let options = CompileOptions::default();
    for result in [
        compile_module_with_context(TOOL_SOURCE, &context).map(|_| ()),
        compile_named_module_with_context("tool.sigil", TOOL_SOURCE, options.clone(), &context)
            .map(|_| ()),
        compile_project_with_context(project_sources(), Some("tool"), options.clone(), &context)
            .map(|_| ()),
        compile_library_project_with_context(project_sources(), options, &context).map(|_| ()),
        compile_tool_with_context(TOOL_SOURCE, &context).map(|_| ()),
        compile_tool_with_limits_and_context(TOOL_SOURCE, &CompileLimits::default(), &context)
            .map(|_| ()),
    ] {
        result.expect("the production v9 verifier authorizes the exact checked profile");
    }
}

fn operation(module: &str, name: &str) -> HostOperationContract {
    HostOperationContract {
        module: module.into(),
        name: name.into(),
        occurrence: OccurrenceVisibility::Public,
        params: vec![],
        results: vec![],
        domains: vec![],
    }
}

fn profile(operations: Vec<HostOperationContract>) -> HostContractProfile {
    HostContractProfile::new("context-test".into(), 1, vec![], operations)
        .expect("test declarations must satisfy host-profile validation")
}

#[test]
fn legacy_context_has_no_requirement_and_refuses_contract_resolution() {
    let legacy = CompilerContext::default();
    assert_eq!(legacy.host_profile(), None);
    assert_eq!(legacy.canonical_host_profile_bytes(), None);
    assert_eq!(legacy.host_profile_fingerprint(), None);
    assert_eq!(legacy.host_requirement(), None);
    assert_eq!(
        legacy.resolve_extern("tick", &[], &[]),
        Err(CompilerContextError::MissingHostProfile)
    );

    let configured = CompilerContext::with_host_profile(profile(vec![operation("ffi", "tick")]));
    assert_eq!(
        configured.resolve_extern("tick", &[], &[]),
        Ok(&operation("ffi", "tick"))
    );
    assert!(configured.host_requirement().is_some());
}

#[test]
fn cloned_contexts_share_the_immutable_profile() {
    let shared = Arc::new(profile(vec![operation("ffi", "tick")]));
    let first = CompilerContext::with_host_profile(Arc::clone(&shared));
    let second = first.clone();
    assert!(std::ptr::eq(
        first
            .host_profile()
            .expect("configured context has a profile"),
        shared.as_ref()
    ));
    assert!(std::ptr::eq(
        first
            .host_profile()
            .expect("configured context has a profile"),
        second
            .host_profile()
            .expect("cloning preserves the profile")
    ));
}

#[test]
fn extern_resolution_never_falls_back_to_another_module_or_name() {
    let wrong_module = CompilerContext::with_host_profile(profile(vec![operation("host", "tick")]));
    assert_eq!(
        wrong_module.resolve_extern("tick", &[], &[]),
        Err(CompilerContextError::HostContract(
            HostContractError::UnknownOperation {
                module: "ffi".into(),
                name: "tick".into(),
            }
        ))
    );

    let exact = operation("ffi", "tick");
    let configured =
        CompilerContext::with_host_profile(profile(vec![operation("host", "tick"), exact.clone()]));
    assert_eq!(configured.resolve_extern("tick", &[], &[]), Ok(&exact));
    assert_eq!(
        configured.resolve_extern("Tick", &[], &[]),
        Err(CompilerContextError::HostContract(
            HostContractError::UnknownOperation {
                module: "ffi".into(),
                name: "Tick".into(),
            }
        ))
    );
}

#[test]
fn extern_resolution_matches_the_emitted_import_identity_and_signature() {
    let source = r#"
#[ring(outer)] #[trusted]
module external_context;
extern "C" fn context_tick(value: i64) -> i64 ! { FFI, Unsafe };
fn run(value: i64) -> i64 @Internal ! { FFI, Unsafe } {
    return context_tick(value);
}
"#;
    let compilation = sigil_compiler::compile_named_module("external_context.sigil", source)
        .expect("legacy trusted extern compilation must remain valid");
    let mut contract = operation("ffi", "context_tick");
    contract.params = vec![HostValueContract {
        ty: HostValueType::I64,
        label: SecurityLabel::Public,
    }];
    contract.results = vec![HostValueContract {
        ty: HostValueType::I64,
        label: SecurityLabel::Internal,
    }];
    let configured = CompilerContext::with_host_profile(profile(vec![contract.clone()]));
    let wasm = compilation
        .wasm_outer
        .as_deref()
        .expect("an outer module must have outer Wasm");
    let mut types = Vec::new();
    let mut matching_imports = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(wasm) {
        match payload.expect("compiler-emitted Wasm must parse") {
            wasmparser::Payload::TypeSection(reader) => {
                types = reader
                    .into_iter_err_on_gc_types()
                    .collect::<Result<Vec<_>, _>>()
                    .expect("compiler emits ordinary Wasm function types");
            }
            wasmparser::Payload::ImportSection(reader) => {
                for import in reader.into_imports() {
                    let import = import.expect("compiler-emitted import must parse");
                    if import.name == "context_tick" {
                        matching_imports.push((import.module.to_owned(), import.ty));
                    }
                }
            }
            _ => {}
        }
    }
    assert_eq!(
        matching_imports.len(),
        1,
        "the extern must be imported exactly once"
    );
    let (module, ty) = &matching_imports[0];
    assert_eq!(module, &contract.module);
    let wasmparser::TypeRef::Func(index) = ty else {
        panic!("the source extern must emit a function import");
    };
    let signature = &types[*index as usize];
    assert_eq!(signature.params(), &[wasmparser::ValType::I64]);
    assert_eq!(signature.results(), &[wasmparser::ValType::I64]);
    assert_eq!(
        configured.resolve_extern("context_tick", &[HostValueType::I64], &[HostValueType::I64]),
        Ok(&contract)
    );
}

#[test]
fn extern_resolution_rejects_unsupported_source_identity_without_normalizing() {
    let configured = CompilerContext::with_host_profile(profile(vec![operation("ffi", "_tick9")]));
    assert!(configured.resolve_extern("_tick9", &[], &[]).is_ok());
    for name in [
        "",
        "9tick",
        "ffi::_tick9",
        "module::_tick9",
        "_tick9/x",
        " _tick9",
        "_tick9 ",
        "_tíck9",
        "_tick9\0",
    ] {
        assert_eq!(
            configured.resolve_extern(name, &[], &[]),
            Err(CompilerContextError::UnsupportedExternName(name.into()))
        );
    }
    let oversized = "x".repeat(MAX_HOST_NAME_BYTES + 1);
    assert_eq!(
        configured.resolve_extern(&oversized, &[], &[]),
        Err(CompilerContextError::UnsupportedExternName(oversized))
    );
    let maximum = "x".repeat(MAX_HOST_NAME_BYTES);
    let boundary = CompilerContext::with_host_profile(profile(vec![operation("ffi", &maximum)]));
    assert_eq!(
        boundary.resolve_extern(&maximum, &[], &[]),
        Ok(&operation("ffi", &maximum))
    );
}

#[test]
fn extern_resolution_checks_parameter_order_arity_and_result_type() {
    let mut call = operation("ffi", "convert");
    call.params = vec![
        HostValueContract {
            ty: HostValueType::I32,
            label: SecurityLabel::Public,
        },
        HostValueContract {
            ty: HostValueType::I64,
            label: SecurityLabel::Public,
        },
    ];
    call.results = vec![HostValueContract {
        ty: HostValueType::F64,
        label: SecurityLabel::Public,
    }];
    let configured = CompilerContext::with_host_profile(profile(vec![call.clone()]));
    assert_eq!(
        configured.resolve_extern(
            "convert",
            &[HostValueType::I32, HostValueType::I64],
            &[HostValueType::F64],
        ),
        Ok(&call)
    );
    for (params, results) in [
        (
            vec![HostValueType::I64, HostValueType::I32],
            vec![HostValueType::F64],
        ),
        (vec![HostValueType::I32], vec![HostValueType::F64]),
        (
            vec![HostValueType::I32, HostValueType::I64],
            vec![HostValueType::I64],
        ),
        (vec![HostValueType::I32, HostValueType::I64], vec![]),
        (
            vec![HostValueType::I32, HostValueType::I64],
            vec![HostValueType::F64; 2],
        ),
    ] {
        assert_eq!(
            configured.resolve_extern("convert", &params, &results),
            Err(CompilerContextError::HostContract(
                HostContractError::SignatureMismatch {
                    module: "ffi".into(),
                    name: "convert".into(),
                }
            ))
        );
    }
}

#[test]
fn occurrence_is_independent_of_secret_parameters_results_and_empty_payloads() {
    let mut private = operation("ffi", "private_tick");
    private.occurrence = OccurrenceVisibility::Secret;
    private.results = vec![HostValueContract {
        ty: HostValueType::I64,
        label: SecurityLabel::Secret,
    }];
    let mut public = operation("ffi", "public_secret");
    public.params = private.results.clone();
    public.results = private.results.clone();
    let configured =
        CompilerContext::with_host_profile(profile(vec![private.clone(), public.clone()]));
    assert_eq!(
        configured.resolve_extern("private_tick", &[], &[HostValueType::I64]),
        Ok(&private)
    );
    assert_eq!(
        configured.resolve_extern(
            "public_secret",
            &[HostValueType::I64],
            &[HostValueType::I64]
        ),
        Ok(&public)
    );
    assert_eq!(private.occurrence, OccurrenceVisibility::Secret);
    assert_eq!(public.occurrence, OccurrenceVisibility::Public);
}

#[test]
fn production_v9_enforces_actual_ffi_arguments_against_the_bound_profile() {
    let source = r#"
#[ring(outer)] #[trusted]
module ffi_argument_policy;
extern "C" fn context_tick(value: i64) -> i64 ! { FFI, Unsafe };
fn run(value: i64 @Internal) -> i64 @Internal ! { FFI, Unsafe } {
    return context_tick(value);
}
"#;
    let contract = |label| {
        let mut operation = operation("ffi", "context_tick");
        operation.params = vec![HostValueContract {
            ty: HostValueType::I64,
            label,
        }];
        operation.results = vec![HostValueContract {
            ty: HostValueType::I64,
            label: SecurityLabel::Internal,
        }];
        operation
    };

    let accepting =
        CompilerContext::with_host_profile(profile(vec![contract(SecurityLabel::Internal)]));
    let compilation = sigil_compiler::compile_named_module_with_context(
        "ffi_argument_policy.sigil",
        source,
        sigil_compiler::CompileOptions::default(),
        &accepting,
    )
    .expect("an Internal argument may flow to an Internal host parameter");
    assert_eq!(compilation.formal_security_report.model_version, 9);

    let rejecting =
        CompilerContext::with_host_profile(profile(vec![contract(SecurityLabel::Public)]));
    let error = sigil_compiler::compile_named_module_with_context(
        "ffi_argument_policy.sigil",
        source,
        sigil_compiler::CompileOptions::default(),
        &rejecting,
    )
    .expect_err("an Internal argument must not be laundered through a Public host parameter");
    assert_eq!(
        error
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str())
            .collect::<Vec<_>>(),
        vec!["I013"]
    );
    assert!(error.diagnostics()[0].message().contains("detail=40"));
}

#[test]
fn canonical_profile_fingerprint_and_requirement_match_the_pinned_vector() {
    // The wire bytes and SHA-256 digest are a fixed independent oracle, not an
    // expectation computed through the implementation being checked. Changing
    // the profile format requires reviewing both this vector and the ABI version.
    const CANONICAL: &[u8] = b"SIGIL-HOST-PROFILE\0\x01\0\0\0\x0c\0\0\0context-test\x01\0\0\0\0\0\0\0\0\0\0\0\x01\0\0\0\x03\0\0\0ffi\x04\0\0\0tick\0\0\0\0\0\0\0\0\0\0\0\0\0";
    const FINGERPRINT: [u8; 32] = [
        0xa5, 0x10, 0x43, 0xf9, 0xe8, 0x1e, 0x73, 0xaf, 0x76, 0xb8, 0x41, 0xba, 0xd3, 0xeb, 0x5d,
        0x69, 0xd6, 0x1b, 0xac, 0x18, 0x17, 0x89, 0x10, 0xa7, 0xf1, 0x31, 0xfd, 0x39, 0xff, 0x14,
        0x3b, 0x9b,
    ];
    let configured = CompilerContext::with_host_profile(profile(vec![operation("ffi", "tick")]));
    assert_eq!(configured.canonical_host_profile_bytes(), Some(CANONICAL));
    assert_eq!(configured.host_profile_fingerprint(), Some(FINGERPRINT));
    let requirement = configured
        .host_requirement()
        .expect("configured profile has a requirement");
    assert_eq!(requirement.fingerprint, FINGERPRINT);
    let mut expected_requirement = [0; 36];
    expected_requirement[0] = 1;
    expected_requirement[4..].copy_from_slice(&FINGERPRINT);
    assert_eq!(requirement.encode(), expected_requirement);
    assert_eq!(
        HostProfileRequirement::decode(&expected_requirement),
        Ok(requirement)
    );

    // A one-field mutation proves the fingerprint comparison detects profile
    // drift; a decoded declaration still only requests that exact profile.
    let changed = HostContractProfile::new(
        "context-test".into(),
        2,
        vec![],
        vec![operation("ffi", "tick")],
    )
    .expect("changing a nonzero revision preserves profile validity");
    assert_ne!(changed.fingerprint(), FINGERPRINT);
    assert_eq!(
        changed.check_required_fingerprint(&requirement.fingerprint),
        Err(HostContractError::ProfileMismatch)
    );
    let decoded = HostContractProfile::decode(CANONICAL).expect("pinned canonical profile decodes");
    assert_eq!(
        CompilerContext::with_host_profile(decoded).host_requirement(),
        Some(requirement)
    );
}
