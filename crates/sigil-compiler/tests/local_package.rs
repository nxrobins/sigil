//! Executable obligations for the offline local-package seam.
//!
//! The checked-in fixture is neutral infrastructure, not a candidate package.
//! Semantic mutations are copied to a temporary tree and re-locked so the
//! intended compiler boundary—not an incidental stale hash—owns the verdict.

// The package compiler's secure traversal is fd-based and refuses on non-unix
// platforms by design (E_UNSUPPORTED_PLATFORM). Every test below compiles a
// package, so the whole binary is unix-only; the refusal contract itself is
// asserted on other platforms by package_cli's
// `package_compile_fails_closed_where_secure_traversal_is_unavailable`.
#![cfg(unix)]

use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;
use sha2::{Digest, Sha256};
use sigil_compiler::CompileOptions;
use sigil_compiler::package::{
    PackageCompilation, PackageCompileError, PackageError,
    compile_local_package as compile_local_package_accepting, compiler_stdlib_hash,
    verify_local_package_certificate as verify_local_package_certificate_accepting,
};
#[cfg(not(feature = "solver"))]
use sigil_compiler::package::{
    compile_local_package_structural, verify_local_package_certificate_structural,
};
use tempfile::TempDir;

const FIXTURE: &str = "tests/fixtures/packages/neutral-boundaries";
const CONTENT_DOMAIN: &[u8] = b"SIGIL-PACKAGE-CONTENT\0V1\0";
const GRAPH_DOMAIN: &[u8] = b"SIGIL-PACKAGE-GRAPH\0V1\0";

fn fixture_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(FIXTURE)
}

fn compile_local_package(
    root: &Path,
    options: CompileOptions,
) -> Result<PackageCompilation, PackageCompileError> {
    #[cfg(feature = "solver")]
    {
        compile_local_package_accepting(root, options)
    }
    #[cfg(not(feature = "solver"))]
    {
        compile_local_package_structural(root, options)
    }
}

fn verify_local_package_certificate(
    root: &Path,
    supplied: &sigil_compiler::package::PackageCertificateJson,
    options: CompileOptions,
) -> Result<PackageCompilation, PackageCompileError> {
    #[cfg(feature = "solver")]
    {
        verify_local_package_certificate_accepting(root, supplied, options)
    }
    #[cfg(not(feature = "solver"))]
    {
        verify_local_package_certificate_structural(root, supplied, options)
    }
}

fn copy_fixture() -> (TempDir, PathBuf) {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().join("fixture");
    copy_tree(&fixture_root(), &root);
    (temp, root)
}

fn copy_tree(from: &Path, to: &Path) {
    copy_tree_with_creation_order(from, to, false);
}

fn copy_tree_reversed(from: &Path, to: &Path) {
    copy_tree_with_creation_order(from, to, true);
}

fn copy_tree_with_creation_order(from: &Path, to: &Path, reverse: bool) {
    fs::create_dir_all(to).unwrap();
    let mut entries: Vec<_> = fs::read_dir(from).unwrap().map(Result::unwrap).collect();
    entries.sort_by_key(|entry| entry.file_name());
    if reverse {
        entries.reverse();
    }
    for entry in entries {
        let source = entry.path();
        let target = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree_with_creation_order(&source, &target, reverse);
        } else {
            fs::copy(source, target).unwrap();
        }
    }
}

fn package_error(
    result: Result<sigil_compiler::package::PackageCompilation, PackageCompileError>,
) -> PackageError {
    match result {
        Err(PackageCompileError::Package(error)) => error,
        Err(PackageCompileError::Compiler(error)) => panic!(
            "expected package error, got compiler diagnostics: {:?}",
            error.diagnostics()
        ),
        Ok(_) => panic!("package check should fail"),
    }
}

fn compiler_codes(
    result: Result<sigil_compiler::package::PackageCompilation, PackageCompileError>,
) -> Vec<String> {
    match result.expect_err("package check should fail") {
        PackageCompileError::Compiler(error) => error
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str().to_owned())
            .collect(),
        PackageCompileError::Package(error) => panic!("expected compiler error, got {error}"),
    }
}

fn json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).unwrap()).unwrap()
}

fn write_json(path: &Path, value: &Value) {
    let mut bytes = serde_json::to_vec_pretty(value).unwrap();
    bytes.push(b'\n');
    fs::write(path, bytes).unwrap();
}

fn normalize(source: &str) -> Vec<u8> {
    let source = source.replace("\r\n", "\n").replace('\r', "\n");
    let mut normalized = source
        .split('\n')
        .map(|line| line.trim_end_matches([' ', '\t']))
        .collect::<Vec<_>>()
        .join("\n");
    if !normalized.ends_with('\n') {
        normalized.push('\n');
    }
    normalized.into_bytes()
}

fn frame(digest: &mut Sha256, value: &[u8]) {
    digest.update((value.len() as u64).to_be_bytes());
    digest.update(value);
}

fn canonical(value: &Value) -> Vec<u8> {
    serde_json::to_vec(value).unwrap()
}

fn package_hashes(root: &Path, identity: &str) -> (String, String) {
    let manifest_path = root.join("sigil-package.json");
    let manifest = json(&manifest_path);
    let canonical_manifest = canonical(&manifest);
    let manifest_hash = format!("sha256:{:x}", Sha256::digest(&canonical_manifest));
    let version = manifest["version"].as_str().unwrap();
    let mut digest = Sha256::new();
    digest.update(CONTENT_DOMAIN);
    frame(&mut digest, identity.as_bytes());
    frame(&mut digest, version.as_bytes());
    frame(&mut digest, &canonical_manifest);
    let mut modules: Vec<_> = manifest["modules"]
        .as_array()
        .unwrap()
        .iter()
        .map(|module| module.as_str().unwrap().to_owned())
        .collect();
    modules.sort();
    for module in modules {
        let relative = format!("src/{module}.sigil");
        frame(&mut digest, module.as_bytes());
        frame(&mut digest, relative.as_bytes());
        frame(
            &mut digest,
            &normalize(&fs::read_to_string(root.join(relative)).unwrap()),
        );
    }
    (manifest_hash, format!("sha256:{:x}", digest.finalize()))
}

fn graph_hash(nodes: &[Value]) -> String {
    let mut digest = Sha256::new();
    digest.update(GRAPH_DOMAIN);
    for node in nodes {
        for pointer in [
            "/package",
            "/version",
            "/source/kind",
            "/source/locator",
            "/manifest_hash",
            "/content_hash",
        ] {
            frame(
                &mut digest,
                node.pointer(pointer).unwrap().as_str().unwrap().as_bytes(),
            );
        }
        for field in ["features", "modules", "dependencies"] {
            frame(&mut digest, &canonical(&node[field]));
        }
    }
    format!("sha256:{:x}", digest.finalize())
}

/// Rebuild the exact two-node fixture lock after a semantic mutation. This is
/// test-only machinery: production package checking never writes or repairs a lock.
fn relock(root: &Path) {
    let helper_root = root.join("deps/helper");
    relock_with_helper_root(root, &helper_root);
}

fn relock_with_helper_root(root: &Path, helper_root: &Path) {
    let (helper_manifest, helper_content) = package_hashes(helper_root, "test/helper");

    let mut root_manifest = json(&root.join("sigil-package.json"));
    root_manifest["dependencies"][0]["content_hash"] = Value::String(helper_content.clone());
    write_json(&root.join("sigil-package.json"), &root_manifest);
    let (app_manifest, app_content) = package_hashes(root, "test/app");

    let mut lock = json(&root.join("sigil-package.lock.json"));
    lock["nodes"][0]["manifest_hash"] = Value::String(helper_manifest);
    lock["nodes"][0]["content_hash"] = Value::String(helper_content);
    lock["nodes"][1]["manifest_hash"] = Value::String(app_manifest.clone());
    lock["nodes"][1]["content_hash"] = Value::String(app_content);
    lock["root_manifest_hash"] = Value::String(app_manifest);
    lock["stdlib_hash"] = Value::String(compiler_stdlib_hash());
    let hash = graph_hash(lock["nodes"].as_array().unwrap());
    lock["graph_hash"] = Value::String(hash);
    write_json(&root.join("sigil-package.lock.json"), &lock);
}

fn move_helper_to_vendored_source(root: &Path) -> PathBuf {
    let vendor = root.join("vendor");
    fs::create_dir(&vendor).unwrap();
    let helper_root = vendor.join("helper");
    fs::rename(root.join("deps/helper"), &helper_root).unwrap();

    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["dependencies"][0]["source"] = Value::String("vendored".to_owned());
    write_json(&manifest_path, &manifest);

    let lock_path = root.join("sigil-package.lock.json");
    let mut lock = json(&lock_path);
    lock["nodes"][0]["source"]["kind"] = Value::String("vendored".to_owned());
    lock["nodes"][0]["source"]["locator"] = Value::String("helper".to_owned());
    write_json(&lock_path, &lock);
    relock_with_helper_root(root, &helper_root);
    helper_root
}

/// Build a schema-complete, authority-empty synthetic package manifest. Tests
/// mutate only the fields relevant to their obligation, so an incidental
/// manifest omission cannot own the verdict.
fn neutral_manifest(namespace: &str, name: &str, module: &str) -> Value {
    serde_json::json!({
        "compiler": {"features": [], "requires": ">=0.1.0"},
        "declared": {
            "determinism": "pure",
            "effects": [],
            "grant_categories": [],
            "host_imports": [],
            "resource_contract_ref": "tests/fixtures/packages/neutral-boundaries/OBLIGATIONS.md",
            "rings": ["inner"],
            "stable_errors": [],
            "taint_contracts": [],
            "trap_conditions": [],
            "trusted_surface": []
        },
        "dependencies": [],
        "description": "Synthetic package-boundary regression fixture.",
        "evidence": {
            "api_card_hash": "sha256:1111111111111111111111111111111111111111111111111111111111111111",
            "api_contract_hash": "sha256:2222222222222222222222222222222222222222222222222222222222222222",
            "charter_hash": "sha256:3333333333333333333333333333333333333333333333333333333333333333",
            "evidence_manifest_hash": "sha256:4444444444444444444444444444444444444444444444444444444444444444"
        },
        "features": {"available": {}, "default": []},
        "format_version": "1",
        "license": "CC0-1.0",
        "maturity": "contracted",
        "modules": [module],
        "name": name,
        "namespace": namespace,
        "version": "1.0.0"
    })
}

fn create_neutral_package(root: &Path, namespace: &str, name: &str, module: &str, source: &str) {
    fs::create_dir_all(root.join("src")).unwrap();
    write_json(
        &root.join("sigil-package.json"),
        &neutral_manifest(namespace, name, module),
    );
    fs::write(root.join(format!("src/{module}.sigil")), source).unwrap();
}

fn dependency_claim(package: &str, content_hash: &str, features: &[&str]) -> Value {
    serde_json::json!({
        "content_hash": content_hash,
        "default_features": true,
        "features": features,
        "optional": false,
        "package": package,
        "requirement": "=1.0.0",
        "source": "workspace"
    })
}

fn set_dependencies(root: &Path, mut dependencies: Vec<Value>) {
    dependencies.sort_by(|left, right| {
        left["package"]
            .as_str()
            .unwrap()
            .cmp(right["package"].as_str().unwrap())
    });
    let path = root.join("sigil-package.json");
    let mut manifest = json(&path);
    manifest["dependencies"] = Value::Array(dependencies);
    write_json(&path, &manifest);
}

fn locked_node(
    root: &Path,
    package: &str,
    locator: &str,
    features: &[&str],
    dependencies: &[&str],
) -> Value {
    let manifest = json(&root.join("sigil-package.json"));
    let module_values = manifest["modules"].clone();
    let (manifest_hash, content_hash) = package_hashes(root, package);
    serde_json::json!({
        "content_hash": content_hash,
        "dependencies": dependencies,
        "features": features,
        "manifest_hash": manifest_hash,
        "modules": module_values,
        "package": package,
        "source": {"kind": "workspace", "locator": locator},
        "version": "1.0.0",
        "yanked_observed": false
    })
}

fn write_synthetic_lock(root: &Path, root_package: &str, nodes: Vec<Value>) {
    let root_manifest_hash = package_hashes(root, root_package).0;
    let graph_hash = graph_hash(&nodes);
    write_json(
        &root.join("sigil-package.lock.json"),
        &serde_json::json!({
            "compiler_requires": ">=0.1.0",
            "format_version": "1",
            "graph_hash": graph_hash,
            "nodes": nodes,
            "resolver": {"contract": "sigil-resolver-v1", "offline": true},
            "root": root_package,
            "root_manifest_hash": root_manifest_hash,
            "stdlib_hash": compiler_stdlib_hash()
        }),
    );
}

#[test]
fn neutral_graph_proves_label_preserving_package_calls_and_exact_claims() {
    let package = compile_local_package(&fixture_root(), CompileOptions::default())
        .expect("Public/Internal/Secret label-preserving graph should compile");
    assert_eq!(package.graph.root_package, "test/app");
    assert_eq!(
        package
            .graph
            .certificate_nodes
            .iter()
            .map(|node| node.package.as_str())
            .collect::<Vec<_>>(),
        ["test/helper", "test/app"]
    );
    assert!(package.compilation.effects_required.is_empty());
    assert!(package.compilation.wasm_outer.is_none());
    let certificate = package.certificate();
    let root = certificate
        .packages
        .iter()
        .find(|node| node.package == "test/app")
        .unwrap();
    assert_eq!(root.derived.package_imports, ["test/helper"]);
    assert!(root.derived.ambient_imports.is_empty());
    assert!(certificate.ambient_stdlib.modules.is_empty());
    assert!(certificate.base_certificate.primary_module.is_none());
    assert!(
        certificate
            .graph_resource_evidence_hash
            .starts_with("sha256:")
    );
}

#[test]
fn repeated_package_builds_are_byte_identical() {
    let first = compile_local_package(&fixture_root(), CompileOptions::default()).unwrap();
    let second = compile_local_package(&fixture_root(), CompileOptions::default()).unwrap();
    assert_eq!(first.graph.graph_hash, second.graph.graph_hash);
    assert_eq!(
        first.graph.source_framing_hash,
        second.graph.source_framing_hash
    );
    assert_eq!(first.graph.lockfile_hash, second.graph.lockfile_hash);
    assert_eq!(first.compilation.wasm_inner, second.compilation.wasm_inner);
    assert_eq!(first.compilation.wasm_outer, second.compilation.wasm_outer);
    assert_eq!(
        serde_json::to_vec_pretty(&first.certificate()).unwrap(),
        serde_json::to_vec_pretty(&second.certificate()).unwrap()
    );
}

#[test]
fn reverse_filesystem_creation_order_produces_identical_package_artifacts() {
    let forward_temp = tempfile::tempdir().unwrap();
    let forward_root = forward_temp.path().join("forward");
    copy_tree(&fixture_root(), &forward_root);

    let reverse_temp = tempfile::tempdir().unwrap();
    let reverse_root = reverse_temp.path().join("reverse");
    copy_tree_reversed(&fixture_root(), &reverse_root);

    let forward = compile_local_package(&forward_root, CompileOptions::default()).unwrap();
    let reverse = compile_local_package(&reverse_root, CompileOptions::default()).unwrap();
    assert_eq!(
        forward.graph.certificate_nodes,
        reverse.graph.certificate_nodes
    );
    assert_eq!(forward.graph.graph_hash, reverse.graph.graph_hash);
    assert_eq!(
        forward.graph.source_framing_hash,
        reverse.graph.source_framing_hash
    );
    assert_eq!(forward.graph.lockfile_hash, reverse.graph.lockfile_hash);
    assert_eq!(
        forward.compilation.wasm_inner,
        reverse.compilation.wasm_inner
    );
    assert_eq!(
        forward.compilation.wasm_outer,
        reverse.compilation.wasm_outer
    );
    assert_eq!(
        serde_json::to_vec_pretty(&forward.certificate()).unwrap(),
        serde_json::to_vec_pretty(&reverse.certificate()).unwrap()
    );
    verify_local_package_certificate(
        &forward_root,
        &forward.certificate(),
        CompileOptions::default(),
    )
    .unwrap();
    verify_local_package_certificate(
        &reverse_root,
        &reverse.certificate(),
        CompileOptions::default(),
    )
    .unwrap();
}

#[test]
fn package_certificate_verifies_and_replay_after_source_change_fails_closed() {
    let (_temp, root) = copy_fixture();
    let package = compile_local_package(&root, CompileOptions::default()).unwrap();
    let certificate = package.certificate();
    verify_local_package_certificate(&root, &certificate, CompileOptions::default()).unwrap();

    let app = root.join("src/app.sigil");
    fs::write(
        &app,
        fs::read_to_string(&app)
            .unwrap()
            .replace("return helper::public_echo(value);", "return value;"),
    )
    .unwrap();
    let error = package_error(verify_local_package_certificate(
        &root,
        &certificate,
        CompileOptions::default(),
    ));
    assert_eq!(error.code, "E_HASH_MISMATCH");
}

#[cfg(not(feature = "solver"))]
#[test]
fn accepting_package_apis_fail_closed_without_a_solver_witness() {
    let root = fixture_root();
    let structural = compile_local_package_structural(&root, CompileOptions::default())
        .expect("explicit structural compilation should remain available for diagnostics");
    let certificate = structural.certificate();

    let compile_error = package_error(compile_local_package_accepting(
        &root,
        CompileOptions::default(),
    ));
    assert_eq!(compile_error.code, "E_SOLVER_UNVERIFIED");

    verify_local_package_certificate_structural(&root, &certificate, CompileOptions::default())
        .expect("the explicitly structural comparator should re-derive an exact match");
    let verify_error = package_error(verify_local_package_certificate_accepting(
        &root,
        &certificate,
        CompileOptions::default(),
    ));
    assert_eq!(verify_error.code, "E_SOLVER_UNVERIFIED");
}

#[test]
fn malformed_package_certificate_is_rejected_by_strict_shape() {
    let package = compile_local_package(&fixture_root(), CompileOptions::default()).unwrap();
    let mut value = serde_json::to_value(package.certificate()).unwrap();
    value.as_object_mut().unwrap().remove("package_graph_hash");
    assert!(
        serde_json::from_value::<sigil_compiler::package::PackageCertificateJson>(value).is_err()
    );
}

#[test]
fn graph_order_framing_compiler_and_stdlib_certificate_tampering_fail_closed() {
    let package = compile_local_package(&fixture_root(), CompileOptions::default()).unwrap();
    let clean = package.certificate();
    for field in ["order", "framing", "compiler", "stdlib"] {
        let mut tampered = clean.clone();
        match field {
            "order" => tampered.packages.reverse(),
            "framing" => {
                tampered.composed_source_framing_hash =
                    "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                        .to_owned()
            }
            "compiler" => {
                tampered.compiler_identity_hash =
                    "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                        .to_owned()
            }
            "stdlib" => {
                tampered.stdlib_hash =
                    "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
                        .to_owned()
            }
            _ => unreachable!(),
        }
        let error = package_error(verify_local_package_certificate(
            &fixture_root(),
            &tampered,
            CompileOptions::default(),
        ));
        assert_eq!(error.code, "E_CERTIFICATE", "field {field}");
    }
}

#[test]
fn package_context_rederivation_binds_the_exact_model_nine_profile_report() {
    use sigil_abi::host_contract::HostContractProfile;
    use sigil_compiler::CompilerContext;
    use sigil_compiler::package::{
        compile_local_package_structural_with_context,
        verify_local_package_certificate_structural_with_context,
    };

    let root = fixture_root();
    let legacy = compile_local_package(&root, CompileOptions::default())
        .expect("neutral package compiles through its configured verification tier");
    let certificate = legacy.certificate();
    let empty = CompilerContext::default();
    let explicit =
        compile_local_package_structural_with_context(&root, CompileOptions::default(), &empty)
            .expect("explicit legacy context compiles the same neutral package");
    assert_eq!(certificate, explicit.certificate());
    verify_local_package_certificate_structural_with_context(
        &root,
        &certificate,
        CompileOptions::default(),
        &empty,
    )
    .expect("explicit legacy context rederives the same certificate");
    let first_context = CompilerContext::with_host_profile(
        HostContractProfile::new("package-context".into(), 1, vec![], vec![])
            .expect("an empty, named profile is structurally valid"),
    );
    let first = compile_local_package_structural_with_context(
        &root,
        CompileOptions::default(),
        &first_context,
    )
    .expect("the package compiles under the first explicit profile");
    let first_certificate = first.certificate();
    assert_eq!(first_certificate.base_certificate.schema_version, 9);
    let first_report = first_certificate
        .base_certificate
        .formal
        .as_ref()
        .expect("schema-v9 package certificates contain formal evidence");
    assert_eq!(first_report.model_version, 9);
    assert_ne!(certificate, first_certificate);
    verify_local_package_certificate_structural_with_context(
        &root,
        &first_certificate,
        CompileOptions::default(),
        &first_context,
    )
    .expect("the same profile must reproduce the complete package certificate exactly");

    let changed_context = CompilerContext::with_host_profile(
        HostContractProfile::new("package-context".into(), 2, vec![], vec![])
            .expect("the changed profile is structurally valid"),
    );
    let changed = compile_local_package_structural_with_context(
        &root,
        CompileOptions::default(),
        &changed_context,
    )
    .expect("the same package compiles under the changed profile");
    let changed_certificate = changed.certificate();
    let changed_report = changed_certificate
        .base_certificate
        .formal
        .as_ref()
        .expect("the changed package certificate contains formal evidence");
    assert_eq!(changed_report.model_version, 9);
    assert_eq!(
        first_report.checker_source_fingerprint,
        changed_report.checker_source_fingerprint,
    );
    assert_ne!(
        first_report.csir_fingerprint,
        changed_report.csir_fingerprint
    );

    for (name, context) in [("legacy", &empty), ("changed", &changed_context)] {
        let error = package_error(verify_local_package_certificate_structural_with_context(
            &root,
            &first_certificate,
            CompileOptions::default(),
            context,
        ));
        assert_eq!(error.code, "E_CERTIFICATE", "context {name}");
    }

    #[cfg(feature = "solver")]
    sigil_compiler::package::verify_local_package_certificate_with_context(
        &root,
        &first_certificate,
        CompileOptions::default(),
        &first_context,
    )
    .expect("the solver-backed acceptance path must use the same explicit context");
}

#[test]
fn package_rederivation_rejects_synthetic_host_profile_artifact_claims() {
    use sigil_abi::host_contract::{HOST_PROFILE_SECTION, HostProfileRequirement};
    use sigil_compiler::certificate::ArtifactFingerprint;

    let root = fixture_root();
    let package = compile_local_package(&root, CompileOptions::default())
        .expect("the unchanged neutral package must compile");
    let clean = package.certificate();
    verify_local_package_certificate(&root, &clean, CompileOptions::default())
        .expect("the unchanged package certificate must pass its re-derivation twin");
    let with_profile = |wasm: &[u8], fingerprint: u8| {
        let payload = HostProfileRequirement {
            fingerprint: [fingerprint; 32],
        }
        .encode();
        let mut bytes = wasm.to_vec();
        bytes.extend_from_slice(&[
            0,
            u8::try_from(1 + HOST_PROFILE_SECTION.len() + payload.len())
                .expect("test custom section fits one LEB byte"),
            u8::try_from(HOST_PROFILE_SECTION.len()).expect("test name fits one LEB byte"),
        ]);
        bytes.extend_from_slice(HOST_PROFILE_SECTION.as_bytes());
        bytes.extend_from_slice(&payload);
        for item in wasmparser::Parser::new(0).parse_all(&bytes) {
            item.expect("the synthetic custom section must preserve parseable Wasm");
        }
        bytes
    };
    let tagged = with_profile(&package.compilation.wasm_inner, 7);
    // Package acceptance re-derives SOURCE and never accepts supplied Wasm.
    // These are hand-tagged artifact claims, not compiler-approved profiles:
    // the fresh source compilation has removed their reserved requirement.
    // Solver-off runs exercise the explicit structural comparator above;
    // solver-on runs exercise the solver-requiring acceptance entry point.
    for (mutation, bytes) in [
        ("removed_by_rederivation", tagged.clone()),
        ("changed", with_profile(&package.compilation.wasm_inner, 8)),
        ("duplicated", with_profile(&tagged, 7)),
    ] {
        let mut synthetic = clean.clone();
        synthetic.base_certificate.wasm_inner_fingerprint = ArtifactFingerprint::new(&bytes);
        let error = package_error(verify_local_package_certificate(
            &root,
            &synthetic,
            CompileOptions::default(),
        ));
        assert_eq!(error.code, "E_CERTIFICATE", "requirement {mutation}");
    }

    let mut changed_native = clean;
    changed_native
        .base_certificate
        .formal
        .as_mut()
        .expect("fresh package certificate has native evidence")
        .checker_source_fingerprint
        .push('0');
    let error = package_error(verify_local_package_certificate(
        &root,
        &changed_native,
        CompileOptions::default(),
    ));
    assert_eq!(error.code, "E_CERTIFICATE");
}

#[test]
fn internal_result_cannot_be_returned_as_public_across_package_boundary() {
    let (_temp, root) = copy_fixture();
    let app = root.join("src/app.sigil");
    let source = fs::read_to_string(&app).unwrap().replace(
        "return helper::public_echo(value);",
        "return helper::internal_echo(value);",
    );
    fs::write(app, source).unwrap();
    relock(&root);
    let codes = compiler_codes(compile_local_package(&root, CompileOptions::default()));
    assert!(codes.contains(&"T001".to_owned()), "codes: {codes:?}");
}

#[test]
fn secret_result_cannot_be_returned_as_public_across_package_boundary() {
    let (_temp, root) = copy_fixture();
    let app = root.join("src/app.sigil");
    let source = fs::read_to_string(&app).unwrap().replace(
        "return helper::public_echo(value);",
        "return helper::secret_echo(value);",
    );
    fs::write(app, source).unwrap();
    relock(&root);
    let codes = compiler_codes(compile_local_package(&root, CompileOptions::default()));
    assert!(codes.contains(&"T001".to_owned()), "codes: {codes:?}");
}

#[test]
fn inner_package_cannot_call_dependency_represented_as_trusted_outer() {
    let (_temp, root) = copy_fixture();
    let helper = root.join("deps/helper/src/helper.sigil");
    let source = fs::read_to_string(&helper).unwrap().replace(
        "module helper;",
        "#[ring(outer)] #[trusted]\nmodule helper;",
    );
    fs::write(helper, source).unwrap();
    let manifest_path = root.join("deps/helper/sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["declared"]["rings"] = serde_json::json!(["trusted_outer"]);
    manifest["declared"]["trusted_surface"] = serde_json::json!(["module:helper"]);
    manifest["declared"]["determinism"] = Value::String("state_relative".to_owned());
    write_json(&manifest_path, &manifest);
    relock(&root);
    let codes = compiler_codes(compile_local_package(&root, CompileOptions::default()));
    assert!(codes.contains(&"R004".to_owned()), "codes: {codes:?}");
}

#[test]
fn compiler_derived_outer_ring_rejects_inner_manifest_understatement() {
    let (_temp, root) = copy_fixture();
    let app = root.join("src/app.sigil");
    fs::write(
        &app,
        "#[ring(outer)]\n\
         module app;\n\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
             return input_ptr + input_len;\n\
         }\n",
    )
    .unwrap();
    relock(&root);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MANIFEST");
    assert!(error.message.contains("rings"), "{}", error.message);
}

#[test]
fn compiler_derived_trusted_surface_rejects_manifest_understatement() {
    let (_temp, root) = copy_fixture();
    let app = root.join("src/app.sigil");
    fs::write(
        &app,
        "#[ring(outer)] #[trusted]\n\
         module app;\n\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
             return input_ptr + input_len;\n\
         }\n",
    )
    .unwrap();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["declared"]["rings"] = serde_json::json!(["trusted_outer"]);
    manifest["declared"]["determinism"] = Value::String("state_relative".to_owned());
    manifest["declared"]["taint_contracts"] =
        serde_json::json!(["app::tool_main(input_ptr:Public,input_len:Public)->Public"]);
    write_json(&manifest_path, &manifest);
    relock(&root);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MANIFEST");
    assert!(
        error.message.contains("trusted_surface"),
        "{}",
        error.message
    );
}

#[test]
fn compiler_derived_effects_override_manifest_understatement() {
    let (_temp, root) = copy_fixture();
    let helper = root.join("deps/helper/src/helper.sigil");
    let source = fs::read_to_string(&helper).unwrap().replace(
        "pub fn public_echo(value: i64 @Public) -> i64 @Public {",
        "pub fn public_echo(value: i64 @Public) -> i64 @Public ! { Alloc } {",
    );
    fs::write(helper, source).unwrap();
    relock(&root);
    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MANIFEST");
    assert!(error.message.contains("effects"), "{}", error.message);
}

#[test]
fn compiler_derived_imports_and_grants_override_manifest_understatement() {
    for (claim_import, expected_field) in [(false, "host_imports"), (true, "grant_categories")] {
        let (_temp, root) = copy_fixture();
        let app_source = root.join("src/app.sigil");
        fs::write(
            &app_source,
            fs::read_to_string(&app_source)
                .unwrap()
                .replace("module app;", "#[ring(outer)] #[trusted]\nmodule app;"),
        )
        .unwrap();
        let helper_source = root.join("deps/helper/src/helper.sigil");
        fs::write(
            &helper_source,
            fs::read_to_string(&helper_source)
                .unwrap()
                .replace(
                    "module helper;",
                    "#[ring(outer)] #[trusted]\nmodule helper;\nextern \"C\" fn host_probe() -> i64 ! { FFI, Unsafe };",
                ),
        )
        .unwrap();

        let app_manifest_path = root.join("sigil-package.json");
        let mut app_manifest = json(&app_manifest_path);
        app_manifest["declared"]["rings"] = serde_json::json!(["trusted_outer"]);
        app_manifest["declared"]["trusted_surface"] = serde_json::json!(["module:app"]);
        app_manifest["declared"]["determinism"] = Value::String("state_relative".to_owned());
        write_json(&app_manifest_path, &app_manifest);

        let helper_manifest_path = root.join("deps/helper/sigil-package.json");
        let mut helper_manifest = json(&helper_manifest_path);
        helper_manifest["declared"]["rings"] = serde_json::json!(["trusted_outer"]);
        helper_manifest["declared"]["effects"] = serde_json::json!(["FFI", "Unsafe"]);
        helper_manifest["declared"]["trusted_surface"] =
            serde_json::json!(["extern:helper::host_probe", "module:helper"]);
        helper_manifest["declared"]["determinism"] = Value::String("state_relative".to_owned());
        helper_manifest["declared"]["taint_contracts"]
            .as_array_mut()
            .unwrap()
            .insert(0, Value::String("helper::host_probe()->Public".to_owned()));
        if claim_import {
            helper_manifest["declared"]["host_imports"] = serde_json::json!(["C::host_probe"]);
        }
        write_json(&helper_manifest_path, &helper_manifest);
        relock(&root);

        let error = package_error(compile_local_package(&root, CompileOptions::default()));
        assert_eq!(error.code, "E_MANIFEST");
        assert!(
            error.message.contains(expected_field),
            "expected {expected_field}: {}",
            error.message
        );
    }
}

#[test]
fn compiler_derived_taint_surface_overrides_manifest_understatement() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("deps/helper/sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["declared"]["taint_contracts"]
        .as_array_mut()
        .unwrap()
        .retain(|value| !value.as_str().unwrap().contains("secret_echo"));
    write_json(&manifest_path, &manifest);
    relock(&root);
    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MANIFEST");
    assert!(
        error.message.contains("taint_contracts"),
        "{}",
        error.message
    );
}

#[test]
fn stale_lock_and_source_substitution_fail_before_compilation() {
    let (_temp, root) = copy_fixture();
    let helper = root.join("deps/helper/src/helper.sigil");
    fs::write(
        &helper,
        fs::read_to_string(&helper)
            .unwrap()
            .replace("return value;", "return value + 1;"),
    )
    .unwrap();
    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_HASH_MISMATCH");
}

#[test]
fn version_and_source_conflicts_fail_with_stable_codes() {
    for (field, value, expected) in [
        ("requirement", "=2.0.0", "E_VERSION_CONFLICT"),
        ("source", "vendored", "E_SOURCE_CONFLICT"),
    ] {
        let (_temp, root) = copy_fixture();
        let manifest_path = root.join("sigil-package.json");
        let mut manifest = json(&manifest_path);
        manifest["dependencies"][0][field] = Value::String(value.to_owned());
        write_json(&manifest_path, &manifest);
        relock(&root);
        let error = package_error(compile_local_package(&root, CompileOptions::default()));
        assert_eq!(error.code, expected, "field {field}: {}", error.message);
    }
}

#[test]
fn yanked_and_noncanonical_lock_order_fail_closed() {
    for mutation in ["yanked", "order"] {
        let (_temp, root) = copy_fixture();
        let path = root.join("sigil-package.lock.json");
        let mut lock = json(&path);
        if mutation == "yanked" {
            lock["nodes"][0]["yanked_observed"] = Value::Bool(true);
        } else {
            lock["nodes"].as_array_mut().unwrap().reverse();
        }
        write_json(&path, &lock);
        let error = package_error(compile_local_package(&root, CompileOptions::default()));
        assert_eq!(
            error.code,
            if mutation == "yanked" {
                "E_YANKED"
            } else {
                "E_LOCK_DRIFT"
            }
        );
    }
}

#[test]
fn malformed_lock_error_precedence_is_independent_of_input_enumeration() {
    let (_left_temp, left) = copy_fixture();
    let (_right_temp, right) = copy_fixture();
    for root in [&left, &right] {
        let path = root.join("sigil-package.lock.json");
        let mut lock = json(&path);
        let nodes = lock["nodes"].as_array_mut().unwrap();
        nodes[0]["version"] = Value::String("01.0.0".to_owned());
        nodes[1]["source"]["kind"] = Value::String("network".to_owned());
        write_json(&path, &lock);
    }
    let right_path = right.join("sigil-package.lock.json");
    let mut right_lock = json(&right_path);
    right_lock["nodes"].as_array_mut().unwrap().reverse();
    write_json(&right_path, &right_lock);

    let left_error = package_error(compile_local_package(&left, CompileOptions::default()));
    let right_error = package_error(compile_local_package(&right, CompileOptions::default()));
    assert_eq!(left_error.code, right_error.code);
    assert_eq!(left_error.message, right_error.message);
}

#[test]
fn missing_dependency_and_offline_source_miss_have_distinct_codes() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["dependencies"][0]["package"] = Value::String("test/missing".to_owned());
    write_json(&manifest_path, &manifest);
    assert_eq!(
        package_error(compile_local_package(&root, CompileOptions::default())).code,
        "E_PACKAGE_MISSING"
    );

    let (_temp, root) = copy_fixture();
    fs::rename(root.join("deps/helper"), root.join("deps/helper-away")).unwrap();
    assert_eq!(
        package_error(compile_local_package(&root, CompileOptions::default())).code,
        "E_OFFLINE_MISS"
    );
}

#[test]
fn duplicate_json_keys_are_rejected_at_nested_depth() {
    let (_temp, root) = copy_fixture();
    let path = root.join("sigil-package.json");
    let source = fs::read_to_string(&path).unwrap().replace(
        "\"api_card_hash\": \"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\",",
        "\"api_card_hash\": \"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\",\n    \"api_card_hash\": \"sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\",",
    );
    fs::write(path, source).unwrap();
    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MANIFEST");
    assert!(
        error.message.contains("duplicate JSON key"),
        "{}",
        error.message
    );
}

#[test]
fn nonoptional_dependency_cycle_is_reported_before_impossible_cyclic_hash_pins() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("deps/helper/sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["dependencies"] = serde_json::json!([{
        "content_hash": "sha256:09de4a7806dd02eddcd09cac357b8fbc06ef08421fcf0ccf2c79830f14203638",
        "default_features": true,
        "features": [],
        "optional": false,
        "package": "test/app",
        "requirement": "=1.0.0",
        "source": "workspace"
    }]);
    write_json(&manifest_path, &manifest);
    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_DEP_CYCLE");
}

#[test]
fn feature_cycles_and_unknown_features_fail_with_stable_codes() {
    for (enabled, expected) in [("loop", "E_FEATURE_CYCLE"), ("ghost", "E_FEATURE_UNKNOWN")] {
        let (_temp, root) = copy_fixture();
        let manifest_path = root.join("sigil-package.json");
        let mut manifest = json(&manifest_path);
        manifest["features"]["default"] = serde_json::json!([enabled]);
        if enabled == "loop" {
            manifest["features"]["available"] = serde_json::json!({
                "loop": {
                    "description": "Intentional feature-cycle fixture.",
                    "enables": ["loop"],
                    "optional_dependencies": []
                }
            });
        }
        write_json(&manifest_path, &manifest);
        relock(&root);
        let lock_path = root.join("sigil-package.lock.json");
        let mut lock = json(&lock_path);
        lock["nodes"][1]["features"] = serde_json::json!([enabled]);
        lock["graph_hash"] = Value::String(graph_hash(lock["nodes"].as_array().unwrap()));
        write_json(&lock_path, &lock);
        let error = package_error(compile_local_package(&root, CompileOptions::default()));
        assert_eq!(error.code, expected);
    }
}

#[test]
fn optional_dependency_feature_expansion_is_locked_and_compiles() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["dependencies"][0]["optional"] = Value::Bool(true);
    manifest["features"]["default"] = serde_json::json!(["helper_feature"]);
    manifest["features"]["available"] = serde_json::json!({
        "helper_feature": {
            "description": "Activates the neutral helper dependency.",
            "enables": [],
            "optional_dependencies": ["test/helper"]
        }
    });
    write_json(&manifest_path, &manifest);
    relock(&root);
    let lock_path = root.join("sigil-package.lock.json");
    let mut lock = json(&lock_path);
    lock["nodes"][1]["features"] = serde_json::json!(["helper_feature"]);
    lock["graph_hash"] = Value::String(graph_hash(lock["nodes"].as_array().unwrap()));
    write_json(&lock_path, &lock);
    compile_local_package(&root, CompileOptions::default())
        .expect("locked optional feature expansion should compile");
}

#[test]
fn exact_locked_vendored_dependency_compiles_offline() {
    let (_temp, root) = copy_fixture();
    move_helper_to_vendored_source(&root);

    let package = compile_local_package(&root, CompileOptions::default())
        .expect("an exact local vendored source should compile offline");
    let helper = package
        .graph
        .certificate_nodes
        .iter()
        .find(|node| node.package == "test/helper")
        .unwrap();
    assert_eq!(helper.source.kind, "vendored");
    assert_eq!(helper.source.locator, "helper");
}

#[cfg(unix)]
#[test]
fn vendored_source_rejects_a_symlinked_vendor_base() {
    use std::os::unix::fs::symlink;

    let (_temp, root) = copy_fixture();
    move_helper_to_vendored_source(&root);
    let outside_vendor = root.parent().unwrap().join("outside-vendor");
    fs::rename(root.join("vendor"), &outside_vendor).unwrap();
    symlink(&outside_vendor, root.join("vendor")).unwrap();

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MANIFEST");
    assert!(error.message.contains("symlink"), "{}", error.message);
}

#[cfg(unix)]
#[test]
fn package_inputs_reject_symlinked_leaf_files() {
    use std::os::unix::fs::symlink;

    for relative in [
        "src/app.sigil",
        "sigil-package.json",
        "sigil-package.lock.json",
    ] {
        let (_temp, root) = copy_fixture();
        let path = root.join(relative);
        let outside = root
            .parent()
            .unwrap()
            .join(format!("outside-{}", relative.replace('/', "-")));
        fs::copy(&path, &outside).unwrap();
        fs::remove_file(&path).unwrap();
        symlink(&outside, &path).unwrap();
        let error = package_error(compile_local_package(&root, CompileOptions::default()));
        assert!(
            matches!(error.code, "E_MANIFEST" | "E_OFFLINE_MISS"),
            "{relative}: {error}"
        );
        assert!(
            error.message.contains("open") || error.message.contains("symlink"),
            "{relative}: {error}"
        );
    }
}

#[test]
fn package_v1_rejects_unattested_authority_and_callable_surfaces() {
    for (kind, declaration) in [
        ("capability type", "pub cap type Gate { read, write }"),
        (
            "actor",
            "pub actor Worker { on Ping(x: i64 @Secret) -> i64 { return 0; } }",
        ),
        (
            "implementation",
            "record Boxed { value: i64 } impl Boxed { pub fn get(self: Boxed) -> i64 { return self.value; } }",
        ),
        (
            "trait",
            "pub trait Readable { fn read(self: Self) -> i64; }",
        ),
        ("typestate", "state File { Open, Closed }"),
    ] {
        let (_temp, root) = copy_fixture();
        let source_path = root.join("src/app.sigil");
        let mut source = fs::read_to_string(&source_path).unwrap();
        source.push('\n');
        source.push_str(declaration);
        source.push('\n');
        fs::write(&source_path, source).unwrap();
        relock(&root);

        let error = package_error(compile_local_package(&root, CompileOptions::default()));
        assert_eq!(error.code, "E_UNSUPPORTED_SURFACE", "{kind}: {error}");
        assert!(error.message.contains(kind), "{kind}: {error}");
    }
}

#[test]
fn package_v1_surface_rejection_covers_dependencies() {
    let (_temp, root) = copy_fixture();
    let source_path = root.join("deps/helper/src/helper.sigil");
    let mut source = fs::read_to_string(&source_path).unwrap();
    source.push_str("\ncap type DependencyGate { read }\n");
    fs::write(&source_path, source).unwrap();
    relock(&root);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_UNSUPPORTED_SURFACE");
    assert!(error.message.contains("test/helper"), "{error}");
    assert!(error.message.contains("capability type"), "{error}");
}

#[test]
fn two_packages_cannot_expose_the_same_module() {
    let (_temp, root) = copy_fixture();
    copy_tree(&root.join("deps/helper"), &root.join("deps/helper-two"));
    let second_manifest_path = root.join("deps/helper-two/sigil-package.json");
    let mut second_manifest = json(&second_manifest_path);
    second_manifest["namespace"] = Value::String("other".to_owned());
    write_json(&second_manifest_path, &second_manifest);

    let root_manifest_path = root.join("sigil-package.json");
    let mut root_manifest = json(&root_manifest_path);
    let mut dependency = root_manifest["dependencies"][0].clone();
    dependency["package"] = Value::String("other/helper".to_owned());
    root_manifest["dependencies"]
        .as_array_mut()
        .unwrap()
        .insert(0, dependency);
    write_json(&root_manifest_path, &root_manifest);

    let lock_path = root.join("sigil-package.lock.json");
    let mut lock = json(&lock_path);
    let mut node = lock["nodes"][0].clone();
    node["package"] = Value::String("other/helper".to_owned());
    node["source"]["locator"] = Value::String("deps/helper-two".to_owned());
    lock["nodes"].as_array_mut().unwrap().insert(0, node);
    write_json(&lock_path, &lock);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MODULE_COLLISION");
}

#[test]
fn package_stdlib_module_collision_is_rejected() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("deps/helper/sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["name"] = Value::String("vec".to_owned());
    manifest["modules"] = serde_json::json!(["vec"]);
    write_json(&manifest_path, &manifest);
    fs::rename(
        root.join("deps/helper/src/helper.sigil"),
        root.join("deps/helper/src/vec.sigil"),
    )
    .unwrap();
    let source = fs::read_to_string(root.join("deps/helper/src/vec.sigil"))
        .unwrap()
        .replace("module helper;", "module vec;");
    fs::write(root.join("deps/helper/src/vec.sigil"), source).unwrap();

    // Rebuild identity edges in both root manifest and lock before hashing.
    let root_manifest_path = root.join("sigil-package.json");
    let mut root_manifest = json(&root_manifest_path);
    root_manifest["dependencies"][0]["package"] = Value::String("test/vec".to_owned());
    write_json(&root_manifest_path, &root_manifest);
    let lock_path = root.join("sigil-package.lock.json");
    let mut lock = json(&lock_path);
    lock["nodes"][0]["package"] = Value::String("test/vec".to_owned());
    lock["nodes"][0]["modules"] = serde_json::json!(["vec"]);
    lock["nodes"][1]["dependencies"] = serde_json::json!(["test/vec"]);
    write_json(&lock_path, &lock);

    // Custom relock for renamed helper identity.
    let (dep_manifest, dep_content) = package_hashes(&root.join("deps/helper"), "test/vec");
    let mut root_manifest = json(&root_manifest_path);
    root_manifest["dependencies"][0]["content_hash"] = Value::String(dep_content.clone());
    write_json(&root_manifest_path, &root_manifest);
    let (app_manifest, app_content) = package_hashes(&root, "test/app");
    let mut lock = json(&lock_path);
    lock["nodes"][0]["manifest_hash"] = Value::String(dep_manifest);
    lock["nodes"][0]["content_hash"] = Value::String(dep_content);
    lock["nodes"][1]["manifest_hash"] = Value::String(app_manifest.clone());
    lock["nodes"][1]["content_hash"] = Value::String(app_content);
    lock["root_manifest_hash"] = Value::String(app_manifest);
    lock["graph_hash"] = Value::String(graph_hash(lock["nodes"].as_array().unwrap()));
    write_json(&lock_path, &lock);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MODULE_COLLISION");
}

#[test]
fn no_entry_library_graph_compiles_and_dependency_entry_is_not_selected() {
    let temp = tempfile::tempdir().unwrap();
    let root = temp.path().join("fixture");
    let helper_root = root.join("deps/helper");
    create_neutral_package(
        &helper_root,
        "test",
        "helper",
        "helper",
        "module helper;\n\nfn helper_value(value: i64) -> i64 {\n    return value;\n}\n",
    );
    create_neutral_package(
        &root,
        "test",
        "app",
        "app",
        "module app;\n\nfn root_value(value: i64) -> i64 {\n    return value;\n}\n",
    );

    let helper_content = package_hashes(&helper_root, "test/helper").1;
    set_dependencies(
        &root,
        vec![dependency_claim("test/helper", &helper_content, &[])],
    );
    write_synthetic_lock(
        &root,
        "test/app",
        vec![
            locked_node(&helper_root, "test/helper", "deps/helper", &[], &[]),
            locked_node(&root, "test/app", ".", &[], &["test/helper"]),
        ],
    );

    let no_entry = compile_local_package(&root, CompileOptions::default())
        .expect("a package graph is a library and needs no executable entry");
    assert_eq!(no_entry.compilation.primary_module_name(), None);
    assert_eq!(no_entry.compilation.module_names, ["app", "helper"]);

    fs::write(
        helper_root.join("src/helper.sigil"),
        "module helper;\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n    return input_ptr + input_len;\n}\n",
    )
    .unwrap();
    let helper_manifest_path = helper_root.join("sigil-package.json");
    let mut helper_manifest = json(&helper_manifest_path);
    helper_manifest["declared"]["taint_contracts"] =
        serde_json::json!(["helper::tool_main(input_ptr:Public,input_len:Public)->Public"]);
    write_json(&helper_manifest_path, &helper_manifest);
    let helper_content = package_hashes(&helper_root, "test/helper").1;
    set_dependencies(
        &root,
        vec![dependency_claim("test/helper", &helper_content, &[])],
    );
    write_synthetic_lock(
        &root,
        "test/app",
        vec![
            locked_node(&helper_root, "test/helper", "deps/helper", &[], &[]),
            locked_node(&root, "test/app", ".", &[], &["test/helper"]),
        ],
    );

    let dependency_entry = compile_local_package(&root, CompileOptions::default())
        .expect("a dependency entry declaration must not hijack package compilation");
    assert_eq!(dependency_entry.compilation.primary_module_name(), None);
    assert_eq!(dependency_entry.compilation.module_names, ["app", "helper"]);
}

#[test]
fn result_and_option_ambient_modules_are_bound_to_the_compiler_stdlib() {
    let (_temp, root) = copy_fixture();
    fs::write(
        root.join("src/app.sigil"),
        "module app;\n\nfn wrap(value: i64) -> Result<i64, i64> {\n    return Ok(value);\n}\n\nfn maybe(value: i64) -> Option<i64> {\n    return Some(value);\n}\n",
    )
    .unwrap();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["declared"]["taint_contracts"] = serde_json::json!([]);
    write_json(&manifest_path, &manifest);
    relock(&root);

    let package = compile_local_package(&root, CompileOptions::default())
        .expect("ambient Result and Option should bind to compiler-owned modules");
    let certificate = package.certificate();
    assert_eq!(certificate.ambient_stdlib.modules, ["option", "result"]);
    assert_eq!(
        package.compilation.module_names,
        ["option", "result", "app", "helper"]
    );
    assert!(certificate.packages.iter().all(|node| {
        !node
            .modules
            .iter()
            .any(|module| module == "option" || module == "result")
    }));
    assert_eq!(certificate.stdlib_hash, compiler_stdlib_hash());
}

#[test]
fn null_evidence_fails_closed() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["evidence"] = Value::Null;
    write_json(&manifest_path, &manifest);
    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MANIFEST");
    assert!(
        error.message.to_ascii_lowercase().contains("evidence"),
        "{}",
        error.message
    );
}

#[test]
fn real_compiler_rejects_schema_invalid_manifest_contract_fields() {
    let cases = [
        ("maturity", "/maturity", serde_json::json!("experimental")),
        ("description", "/description", serde_json::json!("")),
        ("license", "/license", serde_json::json!("")),
        (
            "maintainers",
            "/maintainers",
            serde_json::json!(["z-owner", "a-owner"]),
        ),
        (
            "source length",
            "/source",
            serde_json::json!("x".repeat(1025)),
        ),
        (
            "compiler feature",
            "/compiler/features",
            serde_json::json!(["unknown_feature"]),
        ),
        (
            "determinism",
            "/declared/determinism",
            serde_json::json!("sometimes"),
        ),
        ("ring", "/declared/rings", serde_json::json!(["kernel"])),
        (
            "evidence hash",
            "/evidence/charter_hash",
            serde_json::json!("sha256:not-a-hash"),
        ),
        (
            "deprecation shape",
            "/deprecation",
            serde_json::json!({"migration_ref": "migration.md"}),
        ),
    ];

    for (label, pointer, replacement) in cases {
        let (_temp, root) = copy_fixture();
        let path = root.join("sigil-package.json");
        let mut manifest = json(&path);
        if matches!(pointer, "/maintainers" | "/source" | "/deprecation") {
            manifest
                .as_object_mut()
                .unwrap()
                .insert(pointer.trim_start_matches('/').to_owned(), replacement);
        } else {
            *manifest
                .pointer_mut(pointer)
                .expect("fixture pointer exists") = replacement;
        }
        write_json(&path, &manifest);
        let error = package_error(compile_local_package(&root, CompileOptions::default()));
        assert_eq!(error.code, "E_MANIFEST", "case {label}: {error}");
    }
}

#[test]
fn semver_v1_rejects_invalid_identifiers_and_orders_stable_after_prerelease() {
    for invalid in ["01.0.0", "1.0.0-alpha..1", "1.0.0-01", "1.0.0+build"] {
        let (_temp, root) = copy_fixture();
        let path = root.join("sigil-package.json");
        let mut manifest = json(&path);
        manifest["version"] = Value::String(invalid.to_owned());
        write_json(&path, &manifest);
        let error = package_error(compile_local_package(&root, CompileOptions::default()));
        assert_eq!(error.code, "E_MANIFEST", "invalid version {invalid}");
    }

    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["compiler"]["requires"] = Value::String(">=0.1.0-alpha.1".to_owned());
    write_json(&manifest_path, &manifest);
    let lock_path = root.join("sigil-package.lock.json");
    let mut lock = json(&lock_path);
    lock["compiler_requires"] = Value::String(">=0.1.0-alpha.1".to_owned());
    write_json(&lock_path, &lock);
    relock(&root);
    compile_local_package(&root, CompileOptions::default())
        .expect("stable compiler 0.1.0 must sort after 0.1.0-alpha.1");
}

#[test]
fn manifest_compiler_features_are_enforced_by_the_actual_build() {
    let (_temp, root) = copy_fixture();
    let path = root.join("sigil-package.json");
    let mut manifest = json(&path);
    manifest["compiler"]["features"] = serde_json::json!(["solver"]);
    write_json(&path, &manifest);
    relock(&root);
    let result = compile_local_package(&root, CompileOptions::default());
    if sigil_compiler::SOLVER_ENABLED {
        result.expect("solver-enabled compiler must satisfy the manifest feature");
    } else {
        let error = package_error(result);
        assert_eq!(error.code, "E_MANIFEST");
        assert!(error.message.contains("solver"), "{error}");
    }
}

#[test]
fn dormant_bad_features_fail_closed() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    manifest["features"]["available"] = serde_json::json!({
        "latent_cycle": {
            "description": "A dormant cycle must still be rejected.",
            "enables": ["latent_cycle"],
            "optional_dependencies": []
        }
    });
    write_json(&manifest_path, &manifest);
    relock(&root);
    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_FEATURE_CYCLE");
}

#[test]
fn feature_depth_limit_fails_without_recursion_overflow() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    let mut available = serde_json::Map::new();
    for index in 0..=65 {
        let name = format!("f{index:02}");
        let enables = if index == 65 {
            Vec::new()
        } else {
            vec![Value::String(format!("f{:02}", index + 1))]
        };
        available.insert(
            name,
            serde_json::json!({
                "description": "Depth-limit fixture.",
                "enables": enables,
                "optional_dependencies": []
            }),
        );
    }
    manifest["features"]["available"] = Value::Object(available);
    write_json(&manifest_path, &manifest);
    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_RESOURCE_LIMIT");
    assert!(error.message.contains("feature depth"), "{error}");
}

#[test]
fn equivalent_locator_aliases_are_rejected() {
    for alias in ["deps//helper", "deps/./helper", "deps/helper/"] {
        let (_temp, root) = copy_fixture();
        let lock_path = root.join("sigil-package.lock.json");
        let mut lock = json(&lock_path);
        lock["nodes"][0]["source"]["locator"] = Value::String(alias.to_owned());
        lock["graph_hash"] = Value::String(graph_hash(lock["nodes"].as_array().unwrap()));
        write_json(&lock_path, &lock);

        let error = package_error(compile_local_package(&root, CompileOptions::default()));
        assert_eq!(error.code, "E_MANIFEST", "alias {alias}");
        assert!(
            error.message.contains("normalized"),
            "alias {alias}: {}",
            error.message
        );
    }
}

#[test]
fn manifest_module_binding_survives_ambient_injection_and_rejects_a_name_swap() {
    let (_temp, root) = copy_fixture();
    fs::write(
        root.join("src/app.sigil"),
        "module helper;\n\nfn wrap(value: i64) -> Result<i64, i64> {\n    return Ok(value);\n}\n",
    )
    .unwrap();
    fs::write(
        root.join("deps/helper/src/helper.sigil"),
        "module app;\n\nfn helper_value(value: i64) -> i64 {\n    return value;\n}\n",
    )
    .unwrap();
    for manifest_path in [
        root.join("sigil-package.json"),
        root.join("deps/helper/sigil-package.json"),
    ] {
        let mut manifest = json(&manifest_path);
        manifest["declared"]["taint_contracts"] = serde_json::json!([]);
        write_json(&manifest_path, &manifest);
    }
    relock(&root);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MANIFEST");
    assert!(
        error
            .message
            .contains("must declare exactly manifest module `app`"),
        "{}",
        error.message
    );
    assert!(error.message.contains("helper"), "{}", error.message);
}

#[test]
fn root_cannot_import_an_undeclared_transitive_dependency() {
    let (_temp, root) = copy_fixture();
    let helper_root = root.join("deps/helper");
    let middle_root = root.join("deps/middle");
    create_neutral_package(
        &middle_root,
        "test",
        "middle",
        "middle",
        "module middle;\nuse sigil::helper;\n\npub fn relay(value: i64 @Public) -> i64 @Public {\n    return helper::public_echo(value);\n}\n",
    );
    let helper_content = package_hashes(&helper_root, "test/helper").1;
    set_dependencies(
        &middle_root,
        vec![dependency_claim("test/helper", &helper_content, &[])],
    );
    let middle_manifest_path = middle_root.join("sigil-package.json");
    let mut middle_manifest = json(&middle_manifest_path);
    middle_manifest["declared"]["taint_contracts"] =
        serde_json::json!(["middle::relay(value:Public)->Public"]);
    write_json(&middle_manifest_path, &middle_manifest);
    let middle_content = package_hashes(&middle_root, "test/middle").1;
    set_dependencies(
        &root,
        vec![dependency_claim("test/middle", &middle_content, &[])],
    );
    write_synthetic_lock(
        &root,
        "test/app",
        vec![
            locked_node(&helper_root, "test/helper", "deps/helper", &[], &[]),
            locked_node(
                &middle_root,
                "test/middle",
                "deps/middle",
                &[],
                &["test/helper"],
            ),
            locked_node(&root, "test/app", ".", &[], &["test/middle"]),
        ],
    );

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_DEP_EDGE");
    assert!(error.message.contains("test/app"), "{}", error.message);
    assert!(error.message.contains("test/helper"), "{}", error.message);
    assert!(
        error.message.contains("direct declared dependency"),
        "{}",
        error.message
    );
}

#[test]
fn dependency_cannot_import_or_call_the_root_package() {
    let (_temp, root) = copy_fixture();
    let app_path = root.join("src/app.sigil");
    fs::write(
        &app_path,
        "module app;\n\npub fn root_echo(value: i64 @Public) -> i64 @Public {\n    return value;\n}\n",
    )
    .unwrap();
    let app_manifest_path = root.join("sigil-package.json");
    let mut app_manifest = json(&app_manifest_path);
    app_manifest["declared"]["taint_contracts"] =
        serde_json::json!(["app::root_echo(value:Public)->Public"]);
    write_json(&app_manifest_path, &app_manifest);

    let helper_path = root.join("deps/helper/src/helper.sigil");
    let helper_source = fs::read_to_string(&helper_path)
        .unwrap()
        .replace("module helper;", "module helper;\nuse sigil::app;");
    fs::write(
        &helper_path,
        format!(
            "{helper_source}\npub fn reverse_to_root(value: i64 @Public) -> i64 @Public {{\n    return app::root_echo(value);\n}}\n"
        ),
    )
    .unwrap();
    let helper_manifest_path = root.join("deps/helper/sigil-package.json");
    let mut helper_manifest = json(&helper_manifest_path);
    let helper_claims = helper_manifest["declared"]["taint_contracts"]
        .as_array_mut()
        .unwrap();
    helper_claims.push(Value::String(
        "helper::reverse_to_root(value:Public)->Public".to_owned(),
    ));
    helper_claims.sort_by(|left, right| left.as_str().unwrap().cmp(right.as_str().unwrap()));
    write_json(&helper_manifest_path, &helper_manifest);
    relock(&root);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_DEP_EDGE");
    assert!(error.message.contains("test/helper"), "{}", error.message);
    assert!(error.message.contains("test/app"), "{}", error.message);
    assert!(
        error.message.contains("direct declared dependency"),
        "{}",
        error.message
    );
}

#[test]
fn late_diamond_feature_union_converges_before_lock_comparison() {
    let (_temp, root) = copy_fixture();
    let helper_root = root.join("deps/helper");
    let helper_manifest_path = helper_root.join("sigil-package.json");
    let mut helper_manifest = json(&helper_manifest_path);
    helper_manifest["features"]["available"] = serde_json::json!({
        "alpha": {
            "description": "First diamond request.",
            "enables": [],
            "optional_dependencies": []
        },
        "beta": {
            "description": "Late diamond request.",
            "enables": [],
            "optional_dependencies": []
        }
    });
    write_json(&helper_manifest_path, &helper_manifest);
    let helper_content = package_hashes(&helper_root, "test/helper").1;

    let zlate_root = root.join("deps/zlate");
    create_neutral_package(
        &zlate_root,
        "test",
        "zlate",
        "zlate",
        "module zlate;\nuse sigil::helper;\n\npub fn relay(value: i64 @Public) -> i64 @Public {\n    return helper::public_echo(value);\n}\n",
    );
    let mut zlate_to_helper = dependency_claim("test/helper", &helper_content, &["beta"]);
    zlate_to_helper["default_features"] = Value::Bool(false);
    set_dependencies(&zlate_root, vec![zlate_to_helper]);
    let zlate_manifest_path = zlate_root.join("sigil-package.json");
    let mut zlate_manifest = json(&zlate_manifest_path);
    zlate_manifest["declared"]["taint_contracts"] =
        serde_json::json!(["zlate::relay(value:Public)->Public"]);
    write_json(&zlate_manifest_path, &zlate_manifest);
    let zlate_content = package_hashes(&zlate_root, "test/zlate").1;

    let mut app_to_helper = dependency_claim("test/helper", &helper_content, &["alpha"]);
    app_to_helper["default_features"] = Value::Bool(false);
    let mut app_to_zlate = dependency_claim("test/zlate", &zlate_content, &[]);
    app_to_zlate["default_features"] = Value::Bool(false);
    set_dependencies(&root, vec![app_to_helper, app_to_zlate]);

    write_synthetic_lock(
        &root,
        "test/app",
        vec![
            locked_node(
                &helper_root,
                "test/helper",
                "deps/helper",
                &["alpha", "beta"],
                &[],
            ),
            locked_node(
                &zlate_root,
                "test/zlate",
                "deps/zlate",
                &[],
                &["test/helper"],
            ),
            locked_node(&root, "test/app", ".", &[], &["test/helper", "test/zlate"]),
        ],
    );

    let package = compile_local_package(&root, CompileOptions::default())
        .expect("feature union must converge before comparison with the lock");
    let helper = package
        .graph
        .certificate_nodes
        .iter()
        .find(|node| node.package == "test/helper")
        .unwrap();
    assert_eq!(helper.features, ["alpha", "beta"]);
}

#[test]
fn aggregate_package_node_limit_fails_before_resolution_io() {
    let (_temp, root) = copy_fixture();
    let lock_path = root.join("sigil-package.lock.json");
    let mut lock = json(&lock_path);
    let template = lock["nodes"][0].clone();
    let root_node = lock["nodes"][1].clone();
    let mut nodes = Vec::new();
    for index in 0..256 {
        let name = format!("dep{index:03}");
        let mut node = template.clone();
        node["package"] = Value::String(format!("test/{name}"));
        node["source"]["locator"] = Value::String(format!("deps/{name}"));
        node["modules"] = serde_json::json!([name]);
        nodes.push(node);
    }
    nodes.push(root_node);
    lock["nodes"] = Value::Array(nodes);
    write_json(&lock_path, &lock);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_RESOURCE_LIMIT");
    assert!(error.message.contains("257 nodes"), "{}", error.message);
    assert!(
        error.message.contains("maximum is 256"),
        "{}",
        error.message
    );
}

#[test]
fn manifest_dependency_limit_matches_the_schema_before_resolution() {
    let (_temp, root) = copy_fixture();
    let content_hash = format!("sha256:{}", "a".repeat(64));
    let dependencies = (0..=256)
        .map(|index| {
            let mut dependency = dependency_claim(&format!("test/d{index:03}"), &content_hash, &[]);
            dependency["optional"] = Value::Bool(true);
            dependency
        })
        .collect();
    set_dependencies(&root, dependencies);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_RESOURCE_LIMIT");
    assert!(error.message.contains("257 dependencies"), "{error}");
    assert!(error.message.contains("maximum is 256"), "{error}");
}

#[test]
fn feature_optional_dependency_must_reference_an_optional_declaration() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    assert_eq!(manifest["dependencies"][0]["optional"], Value::Bool(false));
    manifest["features"]["available"] = serde_json::json!({
        "helper_feature": {
            "description": "Invalidly treats a required dependency as optional.",
            "enables": [],
            "optional_dependencies": ["test/helper"]
        }
    });
    write_json(&manifest_path, &manifest);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_MANIFEST");
    assert!(error.message.contains("helper_feature"), "{error}");
    assert!(error.message.contains("optional=false"), "{error}");
}

#[test]
fn aggregate_package_edge_limit_fails_before_missing_dependency_resolution() {
    let (_temp, root) = copy_fixture();
    let path = root.join("sigil-package.lock.json");
    let mut lock = json(&path);
    lock["nodes"][1]["dependencies"] = Value::Array(
        (0..=4096)
            .map(|index| Value::String(format!("test/d{index:04}")))
            .collect(),
    );
    write_json(&path, &lock);
    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_RESOURCE_LIMIT");
    assert!(error.message.contains("edges"), "{error}");
}

#[test]
fn aggregate_package_source_count_is_limited() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    let mut modules = vec!["app".to_owned()];
    for index in 0..255 {
        let module = format!("app_{index:03}");
        fs::write(
            root.join(format!("src/{module}.sigil")),
            format!("module {module};\n"),
        )
        .unwrap();
        modules.push(module);
    }
    modules.sort();
    manifest["modules"] = serde_json::json!(modules);
    write_json(&manifest_path, &manifest);

    let lock_path = root.join("sigil-package.lock.json");
    let mut lock = json(&lock_path);
    lock["nodes"][1]["modules"] = manifest["modules"].clone();
    write_json(&lock_path, &lock);
    relock(&root);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_RESOURCE_LIMIT");
    assert!(
        error.message.contains("sources=257/256"),
        "{}",
        error.message
    );
}

#[test]
fn aggregate_normalized_package_source_bytes_are_limited() {
    let (_temp, root) = copy_fixture();
    let manifest_path = root.join("sigil-package.json");
    let mut manifest = json(&manifest_path);
    let mut modules = vec!["app".to_owned()];
    const SOURCE_BYTES: usize = 1_047_000;
    for index in 0..17 {
        let module = format!("app_blob_{index:02}");
        let prefix = format!("module {module};\n//");
        let mut source = prefix.clone();
        source.push_str(&"x".repeat(SOURCE_BYTES - prefix.len() - 1));
        source.push('\n');
        assert_eq!(source.len(), SOURCE_BYTES);
        fs::write(root.join(format!("src/{module}.sigil")), source).unwrap();
        modules.push(module);
    }
    modules.sort();
    manifest["modules"] = serde_json::json!(modules);
    write_json(&manifest_path, &manifest);

    let lock_path = root.join("sigil-package.lock.json");
    let mut lock = json(&lock_path);
    lock["nodes"][1]["modules"] = manifest["modules"].clone();
    write_json(&lock_path, &lock);
    relock(&root);

    let error = package_error(compile_local_package(&root, CompileOptions::default()));
    assert_eq!(error.code, "E_RESOURCE_LIMIT");
    assert!(
        error.message.contains("normalized package source bytes"),
        "{}",
        error.message
    );
    assert!(error.message.contains("16777216"), "{}", error.message);
}
