//! Host-profile assumptions are part of the executable artifact, not merely
//! compiler-side metadata. These tests pin the exact ABI payload and require
//! every emitted ring to carry one canonical custom section.

use sigil_abi::host_contract::{HOST_PROFILE_SECTION, HostContractProfile, HostProfileRequirement};
use sigil_compiler::source::SourceFile;
use sigil_compiler::{
    CompileOptions, CompilerContext, compile_library_project, compile_library_project_with_context,
};
use wasmparser::{Parser, Payload};

fn profile(revision: u64) -> HostContractProfile {
    HostContractProfile::new("wasm-binding-test".into(), revision, vec![], vec![])
        .expect("an empty operation profile is still a valid explicit requirement")
}

fn two_ring_sources() -> Vec<SourceFile> {
    vec![
        SourceFile::new(
            "inner.sigil",
            "module inner; pub fn inner_value() -> i64 { return 1; }",
        ),
        SourceFile::new(
            "outer.sigil",
            "#[ring(outer)] #[trusted]\nmodule outer;\npub fn outer_value() -> i64 { return 2; }",
        ),
    ]
}

fn profile_sections(wasm: &[u8]) -> Vec<Vec<u8>> {
    Parser::new(0)
        .parse_all(wasm)
        .map(|payload| payload.expect("compiler output must be valid Wasm"))
        .filter_map(|payload| match payload {
            Payload::CustomSection(section) if section.name() == HOST_PROFILE_SECTION => {
                Some(section.data().to_vec())
            }
            _ => None,
        })
        .collect()
}

#[test]
fn configured_profile_is_bound_exactly_once_to_both_wasm_rings() {
    let context = CompilerContext::with_host_profile(profile(7));
    let expected = context
        .host_requirement()
        .expect("configured compilation has a requirement");
    let compilation = compile_library_project_with_context(
        two_ring_sources(),
        CompileOptions::default(),
        &context,
    )
    .expect("a Public two-ring library compiles under the declared profile");
    assert_eq!(compilation.formal_security_report.model_version, 9);

    let outer = compilation
        .wasm_outer
        .as_deref()
        .expect("an outer-ring function produces an outer artifact");
    for wasm in [&compilation.wasm_inner[..], outer] {
        let sections = profile_sections(wasm);
        assert_eq!(sections, vec![expected.encode().to_vec()]);
        assert_eq!(
            HostProfileRequirement::decode(&sections[0]),
            Ok(expected),
            "the runtime-facing ABI decoder must recover the exact checked profile",
        );
    }
}

#[test]
fn legacy_artifacts_remain_unmarked_and_profile_drift_changes_both_artifacts() {
    let legacy = compile_library_project(two_ring_sources(), CompileOptions::default())
        .expect("the legacy no-profile path remains accepted");
    assert!(profile_sections(&legacy.wasm_inner).is_empty());
    assert!(
        profile_sections(
            legacy
                .wasm_outer
                .as_deref()
                .expect("the fixture has an outer artifact")
        )
        .is_empty()
    );

    let first = compile_library_project_with_context(
        two_ring_sources(),
        CompileOptions::default(),
        &CompilerContext::with_host_profile(profile(1)),
    )
    .expect("the first profile compiles");
    let changed = compile_library_project_with_context(
        two_ring_sources(),
        CompileOptions::default(),
        &CompilerContext::with_host_profile(profile(2)),
    )
    .expect("the changed profile compiles");

    assert_ne!(first.wasm_inner, changed.wasm_inner);
    assert_ne!(first.wasm_outer, changed.wasm_outer);
    assert_ne!(
        first.formal_security_report.csir_fingerprint,
        changed.formal_security_report.csir_fingerprint,
        "the exact profile declaration must also be bound into certificate evidence"
    );
    assert_ne!(
        profile_sections(&first.wasm_inner),
        profile_sections(&changed.wasm_inner),
    );
}
