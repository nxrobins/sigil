//! Certificate gating for served tools: a cert-pinned tool boots only
//! when the certificate matches the freshly compiled artifact and the
//! configured grants agree with its gated effects.

mod common;

use common::{ECHO_TOOL, TempDir, json_escaped_path, write_service};
use sigil_compiler::certificate::{ArtifactFingerprint, CertificateJson};
use sigil_compiler::{CompilerContext, compile_named_module, compile_named_module_with_context};
use sigil_serve::config::Config;
use sigil_serve::host::{ToolHost, ToolOutcome};

/// serve builds solver-less by default; these tests exercise the
/// fingerprint/effect gates, not solver verification.
fn allow_unverified() {
    // SAFETY: test-process env toggle; only cert tests read it.
    unsafe { std::env::set_var("SIGIL_ALLOW_UNVERIFIED_CERT", "1") };
}

/// Mint a genuine certificate for `source` the same way `sigil check
/// --cert` does.
fn mint_cert(name: &str, source: &str) -> String {
    let compilation = compile_named_module(name.to_owned(), source.to_owned())
        .expect("tool source compiles for cert minting");
    let cert = CertificateJson::new(
        compilation.source_name.clone(),
        source,
        &compilation.wasm_inner,
        compilation.wasm_outer.as_deref(),
        compilation.primary_module_name().map(str::to_owned),
        compilation.module_names.clone(),
        &compilation.capability_report,
        &compilation.ownership_report,
        &compilation.formal_security_report,
        compilation.effects_required.clone(),
    );
    serde_json::to_string_pretty(&cert).expect("cert serializes")
}

/// Synthetic requirement metadata for artifact-comparison tests only. This
/// does not claim that the compiler emits or approves a host profile.
fn with_test_host_profile(wasm: &[u8], fingerprint: u8) -> Vec<u8> {
    const NAME: &[u8] = b"sigil.host-profile";
    let mut tagged = wasm.to_vec();
    tagged.extend_from_slice(&[
        0,
        u8::try_from(1 + NAME.len() + 36).expect("test section fits one LEB byte"),
        u8::try_from(NAME.len()).expect("test name fits one LEB byte"),
    ]);
    tagged.extend_from_slice(NAME);
    tagged.extend_from_slice(&1_u32.to_le_bytes());
    tagged.extend_from_slice(&[fingerprint; 32]);
    tagged
}

fn boot_with_cert(
    label: &str,
    tool_source: &str,
    cert_json: &str,
    grants_json: &str,
) -> (anyhow::Result<ToolHost>, TempDir) {
    allow_unverified();
    let dir = TempDir::new(label);
    std::fs::write(dir.path().join("tool.cert.json"), cert_json).unwrap();
    let config = format!(
        r#"{{
  "tools": {{ "t": {{ "source": "t.sigil", "cert": "tool.cert.json"{grants_json} }} }},
  "http": {{ "bind": "127.0.0.1:0", "routes": [ {{ "path": "/t", "tool": "t" }} ] }}
}}"#
    );
    let config_path = write_service(dir.path(), &config, &[("t.sigil", tool_source)]);
    let (config, base_dir) = Config::load(&config_path).expect("config parses");
    (ToolHost::from_config(&config, &base_dir), dir)
}

#[test]
fn matching_certificate_boots() {
    let cert = mint_cert("t.sigil", ECHO_TOOL);
    let (host, _dir) = boot_with_cert("cert_ok", ECHO_TOOL, &cert, "");
    host.expect("matching cert must boot");
}

#[test]
fn configured_profile_is_not_ignored_when_booting_a_certified_tool() {
    use sigil_compiler::compiler_context::HostContractProfile;
    let cert = mint_cert("t.sigil", ECHO_TOOL);
    let (legacy, dir) = boot_with_cert("context_cert", ECHO_TOOL, &cert, "");
    legacy.expect("the unchanged legacy certificate is a boot accept twin");
    let (config, base_dir) = Config::load(&dir.path().join("service.json"))
        .expect("boot_with_cert wrote a valid service config");
    ToolHost::from_config_with_context(&config, &base_dir, &CompilerContext::default())
        .expect("an explicit legacy context preserves the certified boot");
    let context = CompilerContext::with_host_profile(
        HostContractProfile::new("serve-context".into(), 1, vec![], vec![])
            .expect("an empty named profile is structurally valid"),
    );
    let error = ToolHost::from_config_with_context(&config, &base_dir, &context)
        .err()
        .expect("a legacy certificate cannot certify a model-9 profile-bound artifact");
    assert_eq!(
        error.to_string(),
        "tool `t`: formal security report or CSIR fingerprint mismatch (R819)"
    );

    let compilation = compile_named_module_with_context(
        "t.sigil".to_owned(),
        ECHO_TOOL.to_owned(),
        Default::default(),
        &context,
    )
    .expect("production v9 accepts the explicit server context");
    assert_eq!(compilation.formal_security_report.model_version, 9);
    let exact = CertificateJson::new(
        compilation.source_name.clone(),
        ECHO_TOOL,
        &compilation.wasm_inner,
        compilation.wasm_outer.as_deref(),
        compilation.primary_module_name().map(str::to_owned),
        compilation.module_names.clone(),
        &compilation.capability_report,
        &compilation.ownership_report,
        &compilation.formal_security_report,
        compilation.effects_required.clone(),
    );
    std::fs::write(
        base_dir.join("tool.cert.json"),
        serde_json::to_string_pretty(&exact).expect("exact certificate serializes"),
    )
    .expect("replace the fixture certificate");
    let host = ToolHost::from_config_with_context(&config, &base_dir, &context)
        .expect("the exact profile-bound report and artifact pass certificate boot");
    // The artifact is bound to the `serve-context` profile, not to the ephemeral host's own
    // declared profile, so the ephemeral executor refuses it as bound to a host this is not.
    match host.execute("t", b"") {
        ToolOutcome::HostError(message) => assert!(
            message.contains("required host profile differs from installed profile"),
            "{message}"
        ),
        _ => panic!("legacy serve execution must not ignore the bound host profile"),
    }
}

#[test]
fn source_rederivation_rejects_synthetic_inner_host_profile_artifact_claims() {
    let compilation = compile_named_module("t.sigil", ECHO_TOOL)
        .expect("the ordinary fixture must compile through the native verifier");
    let clean_json = mint_cert("t.sigil", ECHO_TOOL);
    let clean: CertificateJson =
        serde_json::from_str(&clean_json).expect("the freshly emitted certificate is valid JSON");
    let (host, _dir) = boot_with_cert("profile_clean", ECHO_TOOL, &clean_json, "");
    match host
        .expect("the untouched source and certificate must boot")
        .execute("t", b"ordinary")
    {
        sigil_serve::host::ToolOutcome::Success(bytes) => assert_eq!(bytes, b"ordinary"),
        other => panic!("the clean accept twin must execute successfully: {other:?}"),
    }

    let tagged = with_test_host_profile(&compilation.wasm_inner, 7);
    let fresh = ArtifactFingerprint::new(&compilation.wasm_inner);
    // ToolHost accepts SOURCE, never caller-supplied Wasm. Re-derivation
    // therefore removes this hand-added section, and must reject even when
    // a caller supplies a recomputed hash for a changed or duplicated section.
    // No profile-bearing compiler artifact is asserted by these test fixtures.
    for (mutation, bytes) in [
        ("removed_by_rederivation", tagged.clone()),
        (
            "changed",
            with_test_host_profile(&compilation.wasm_inner, 8),
        ),
        ("duplicated", with_test_host_profile(&tagged, 7)),
    ] {
        let mut synthetic = clean.clone();
        synthetic.wasm_inner_fingerprint = ArtifactFingerprint::new(&bytes);
        let expected = format!(
            "tool `t`: wasm fingerprint mismatch — cert {} ({} bytes), fresh {} ({} bytes)",
            synthetic.wasm_inner_fingerprint.hash,
            synthetic.wasm_inner_fingerprint.bytes,
            fresh.hash,
            fresh.bytes,
        );
        let cert = serde_json::to_string(&synthetic).expect("synthetic certificate serializes");
        let (host, _dir) = boot_with_cert(mutation, ECHO_TOOL, &cert, "");
        let error = host
            .err()
            .expect("a hand-tagged artifact must not authorize source execution");
        // This API returns anyhow rather than a diagnostic enum; exact text
        // pins the artifact gate, not an unrelated parse or solver refusal.
        assert_eq!(error.to_string(), expected, "requirement {mutation}");
    }
}

#[test]
fn source_rederivation_rejects_synthetic_outer_host_profile_artifact_claims() {
    const SOURCE: &str = "#[ring(outer)] module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }";
    let compilation =
        compile_named_module("t.sigil", SOURCE).expect("the ordinary outer-ring tool must compile");
    let outer = compilation
        .wasm_outer
        .as_deref()
        .expect("the fixture must emit outer Wasm");
    let clean_json = mint_cert("t.sigil", SOURCE);
    let clean: CertificateJson =
        serde_json::from_str(&clean_json).expect("freshly emitted certificate is valid JSON");
    let (host, _dir) = boot_with_cert("outer_profile_clean", SOURCE, &clean_json, "");
    host.expect("the unchanged two-artifact certificate must boot");
    let tagged = with_test_host_profile(outer, 7);
    for (mutation, bytes) in [
        ("outer_removed_by_rederivation", tagged.clone()),
        ("outer_changed", with_test_host_profile(outer, 8)),
        ("outer_duplicated", with_test_host_profile(&tagged, 7)),
    ] {
        let mut synthetic = clean.clone();
        synthetic.wasm_outer_fingerprint = Some(ArtifactFingerprint::new(&bytes));
        let cert = serde_json::to_string(&synthetic).expect("synthetic certificate serializes");
        let (host, _dir) = boot_with_cert(mutation, SOURCE, &cert, "");
        let error = host
            .err()
            .expect("outer requirement claims must survive exact re-derivation");
        assert_eq!(
            error.to_string(),
            "tool `t`: outer wasm fingerprint mismatch"
        );
    }
}

#[test]
fn missing_or_changed_native_formal_evidence_refuses_source_rederivation() {
    let clean_json = mint_cert("t.sigil", ECHO_TOOL);
    let clean: CertificateJson =
        serde_json::from_str(&clean_json).expect("freshly emitted certificate is valid JSON");
    let (host, _dir) = boot_with_cert("formal_clean", ECHO_TOOL, &clean_json, "");
    host.expect("the unchanged native report must pass its accept twin");
    for mutation in ["missing", "model", "checker", "csir"] {
        let mut changed = clean.clone();
        if mutation == "missing" {
            changed.formal = None;
        } else {
            let report = changed
                .formal
                .as_mut()
                .expect("fresh certificate has native evidence");
            match mutation {
                "model" => report.model_version += 1,
                "checker" => report.checker_source_fingerprint.push('0'),
                "csir" => report.csir_fingerprint.push('0'),
                _ => unreachable!("the mutation list above is exhaustive"),
            }
        }
        let cert = serde_json::to_string(&changed).expect("changed certificate serializes");
        let (host, _dir) = boot_with_cert(mutation, ECHO_TOOL, &cert, "");
        let error = host
            .err()
            .expect("missing or changed native evidence must refuse boot");
        assert_eq!(
            error.to_string(),
            "tool `t`: formal security report or CSIR fingerprint mismatch (R819)",
            "native evidence {mutation}",
        );
    }
}

#[test]
fn tampered_source_refuses_to_boot() {
    let cert = mint_cert("t.sigil", ECHO_TOOL);
    // One byte of drift after certification.
    let tampered = ECHO_TOOL.replace("module tool;", "module tool;\n// drift");
    let (host, _dir) = boot_with_cert("cert_tamper", &tampered, &cert, "");
    let err = host.err().expect("tampered source must be refused");
    assert!(
        format!("{err:#}").contains("source fingerprint"),
        "got: {err:#}"
    );
}

#[test]
fn grants_the_cert_never_claimed_refuse_to_boot() {
    // The echo tool's cert claims no gated effects; granting fs
    // anyway is an overgrant the gate must reject.
    let dir = TempDir::new("cert_overgrant_dir");
    let fs_dir = dir.path().join("data");
    std::fs::create_dir_all(&fs_dir).unwrap();
    let cert = mint_cert("t.sigil", ECHO_TOOL);
    let grants = format!(
        r#", "grants": {{ "fs": ["{}"] }}"#,
        json_escaped_path(&fs_dir)
    );
    let (host, _dir2) = boot_with_cert("cert_overgrant", ECHO_TOOL, &cert, &grants);
    let err = host.err().expect("overgrant must be refused");
    let message = format!("{err:#}");
    assert!(
        message.contains("disagree") && message.contains("FsIO"),
        "got: {message}"
    );
}

#[test]
fn missing_certificate_file_refuses_to_boot() {
    allow_unverified();
    let dir = TempDir::new("cert_missing");
    let config = r#"{
  "tools": { "t": { "source": "t.sigil", "cert": "nope.cert.json" } },
  "http": { "bind": "127.0.0.1:0", "routes": [ { "path": "/t", "tool": "t" } ] }
}"#;
    let config_path = write_service(dir.path(), config, &[("t.sigil", ECHO_TOOL)]);
    let (config, base_dir) = Config::load(&config_path).expect("config parses");
    let err = ToolHost::from_config(&config, &base_dir)
        .err()
        .expect("missing cert file must be refused");
    assert!(
        format!("{err:#}").contains("failed to read certificate"),
        "got: {err:#}"
    );
}

#[test]
fn garbage_certificate_refuses_to_boot() {
    let (host, _dir) = boot_with_cert("cert_garbage", ECHO_TOOL, "not json at all", "");
    let err = host.err().expect("garbage cert must be refused");
    assert!(
        format!("{err:#}").contains("not valid JSON"),
        "got: {err:#}"
    );
}
