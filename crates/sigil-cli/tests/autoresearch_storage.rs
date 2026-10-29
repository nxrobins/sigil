//! WHY THIS TEST EXISTS. Public checkpoint import must require an operator
//! decision and a fresh solver witness, without weakening the ordinary package
//! gate. Exercise the actual host example, existing grants and native consumer.
#![cfg(unix)]

#[path = "../examples/autoresearch-storage.rs"]
mod host;

use sigil_compiler::package::{
    LocalPackageDependency, create_local_package_lock_with_dependencies,
};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

static SEQUENCE: AtomicU64 = AtomicU64::new(0);

fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}
fn copy(source: &Path, target: &Path) {
    std::fs::create_dir_all(target).expect("owned directory");
    for entry in std::fs::read_dir(source).expect("package") {
        let entry = entry.expect("entry");
        if [".sigil", "__pycache__", "sigil-package.lock.json"]
            .iter()
            .any(|n| entry.file_name() == *n)
        {
            continue;
        }
        let kind = entry.file_type().expect("file type");
        if kind.is_dir() {
            copy(&entry.path(), &target.join(entry.file_name()));
        } else {
            assert!(kind.is_file(), "fixture excludes symlinks");
            std::fs::copy(entry.path(), target.join(entry.file_name())).expect("copy");
        }
    }
}
struct Fixture {
    directory: PathBuf,
    root: PathBuf,
    store: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        Self::with_source(None)
    }
    fn with_source(source: Option<&str>) -> Self {
        let directory = loop {
            let path = std::env::temp_dir().join(format!(
                "sigil-storage-host-{}-{}",
                std::process::id(),
                SEQUENCE.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => break path,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("owned fixture: {e}"),
            }
        };
        let root = directory.join("consumer");
        copy(&repo().join("library/programs/autoresearch-store"), &root);
        if let Some(source) = source {
            std::fs::write(root.join("src/tool.sigil"), source)
                .expect("owned source variant before lock");
        }
        let mut dependencies = Vec::new();
        for name in ["kv", "storage"] {
            let path = directory.join(name);
            copy(&repo().join("library/packages").join(name), &path);
            dependencies.push(LocalPackageDependency {
                package: format!("sigil/{name}"),
                path,
            });
        }
        create_local_package_lock_with_dependencies(&root, &dependencies)
            .expect("fresh storage graph");
        let store = directory.join("store");
        std::fs::create_dir(&store).expect("store");
        Self {
            directory,
            root,
            store,
        }
    }
    fn arguments(&self, input: &[u8], read: bool, write: bool) -> Vec<String> {
        let hex = input.iter().map(|b| format!("{b:02x}")).collect::<String>();
        let mut args = vec![
            "--package".to_owned(),
            self.root.display().to_string(),
            "--input-hex".to_owned(),
            hex,
            "--allow-public-checkpoint-import".to_owned(),
        ];
        for (enabled, name) in [(read, "--kv-read"), (write, "--kv-write")] {
            if enabled {
                args.extend([name.to_owned(), self.store.display().to_string()]);
            }
        }
        args
    }
    #[cfg(feature = "solver")]
    fn compile(&self) -> sigil_compiler::package::PackageCompilation {
        sigil_compiler::package::compile_local_package_with_context(
            &self.root,
            sigil_compiler::CompileOptions::default(),
            &sigil_compiler::CompilerContext::with_host_profile(
                sigil_runtime::ephemeral_host_profile(),
            ),
        )
        .expect("checked graph")
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

#[test]
fn public_checkpoint_policy_is_explicit_and_argument_errors_precede_io() {
    assert_eq!(
        host::run(&[]).expect_err("default closed").to_string(),
        "Public checkpoint import requires --allow-public-checkpoint-import"
    );
    for args in [
        vec![
            "--allow-public-checkpoint-import",
            "--allow-public-checkpoint-import",
        ],
        vec!["--allow-public-checkpoint-import", "--unknown"],
        vec!["--allow-public-checkpoint-import", "--package"],
    ] {
        assert!(host::run(&args.into_iter().map(str::to_owned).collect::<Vec<_>>()).is_err());
    }
    for input in [
        "A0".to_owned(),
        "0".to_owned(),
        "g0".to_owned(),
        "00".repeat(16397),
    ] {
        let args = vec![
            "--allow-public-checkpoint-import".to_owned(),
            "--package".to_owned(),
            "/missing-package".to_owned(),
            "--input-hex".to_owned(),
            input,
        ];
        assert_eq!(
            host::run(&args).expect_err("bad transport").to_string(),
            "input must be bounded lowercase hexadecimal"
        );
    }
}

#[test]
fn storage_consumer_metadata_hashes_and_root_graph_are_current() {
    let root = repo().join("library/programs/autoresearch-store");
    let read = |name: &str| {
        serde_json::from_slice::<serde_json::Value>(&std::fs::read(root.join(name)).expect("file"))
            .expect("JSON")
    };
    let hash = |bytes: &[u8]| {
        format!(
            "sha256:{}",
            ring::digest::digest(&ring::digest::SHA256, bytes)
                .as_ref()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        )
    };
    let manifest = read("sigil-package.json");
    for (field, name) in [
        ("api_card_hash", "api-card.json"),
        ("api_contract_hash", "API.md"),
        ("charter_hash", "README.md"),
        ("evidence_manifest_hash", "tool-inputs.json"),
    ] {
        assert_eq!(
            manifest["evidence"][field],
            hash(&std::fs::read(root.join(name)).expect("input"))
        );
    }
    for (name, expected) in read("tool-inputs.json")["files"]
        .as_object()
        .expect("inventory")
    {
        let mut bytes = std::fs::read(root.join(name)).expect("input");
        assert_eq!(expected, &hash(&bytes));
        bytes.push(b'!');
        assert_ne!(expected, &hash(&bytes), "planted drift");
    }
    let fixture = Fixture::new();
    let lock: serde_json::Value = serde_json::from_slice(
        &std::fs::read(fixture.root.join("sigil-package.lock.json")).expect("lock"),
    )
    .expect("JSON");
    assert_eq!(lock["nodes"].as_array().expect("nodes").len(), 3);
}

#[cfg(not(feature = "solver"))]
#[test]
fn storage_host_refuses_structural_only_compilation() {
    let fixture = Fixture::new();
    let error = host::run(&fixture.arguments(b"AKVR\x01\0\0\0", true, false))
        .expect_err("no structural execution");
    let Some(sigil_compiler::package::PackageCompileError::Package(refusal)) =
        error.downcast_ref::<sigil_compiler::package::PackageCompileError>()
    else {
        panic!("package compilation must refuse before storage execution");
    };
    assert_eq!(refusal.code, "E_SOLVER_UNVERIFIED");
    assert_eq!(std::fs::read_dir(&fixture.store).expect("store").count(), 0);
    std::fs::write(fixture.store.join("positive-control"), b"present")
        .expect("owned detector control");
    assert_eq!(std::fs::read_dir(&fixture.store).expect("store").count(), 1);
}

#[cfg(feature = "solver")]
fn publication(old: &[u8], next: &[u8]) -> Vec<u8> {
    [
        b"AKVP\x01\0\0\0".as_slice(),
        &(old.len() as u32).to_le_bytes(),
        old,
        next,
    ]
    .concat()
}
#[cfg(feature = "solver")]
fn refusal(result: anyhow::Result<serde_json::Value>, code: i64) {
    let error = result.expect_err("native refusal");
    assert!(
        matches!(error.downcast_ref::<sigil_runtime::ToolError>(),
        Some(sigil_runtime::ToolError::Trapped {message}) if message == &format!("tool returned error ({code})")),
        "{error:?}"
    );
}

#[cfg(feature = "solver")]
#[test]
fn storage_host_public_import_preserves_grants_bounds_and_previous_bytes() {
    let fixture = Fixture::new();
    let get = b"AKVR\x01\0\0\0";
    refusal(host::run(&fixture.arguments(get, false, false)), 403);
    refusal(host::run(&fixture.arguments(get, true, false)), 404);
    let first = vec![b'a'; 8192];
    let put = publication(b"", &first);
    let other = fixture.directory.join("other");
    std::fs::create_dir(&other).expect("other explicit grant");
    let mut mixed = fixture.arguments(&put, true, true);
    let index = mixed
        .iter()
        .position(|s| s == "--kv-write")
        .expect("write grant")
        + 1;
    mixed[index] = other.display().to_string();
    assert_eq!(
        host::run(&mixed)
            .expect_err("split-store publication refuses")
            .to_string(),
        "read and write grants must name the same checkpoint store"
    );
    refusal(host::run(&fixture.arguments(&put, true, false)), 403);
    refusal(host::run(&fixture.arguments(&put, false, true)), 403);
    assert_eq!(
        host::run(&fixture.arguments(&put, true, true)).expect("published")["data"]["output"],
        serde_json::json!([])
    );
    let loaded = host::run(&fixture.arguments(get, true, false))
        .expect("imported by explicit operator policy");
    assert_eq!(loaded["data"]["output"], serde_json::json!(first));
    assert_eq!(loaded["data"]["import_policy"], host::IMPORT_POLICY);
    assert_eq!(loaded["data"]["source_label"], "Internal");
    assert_eq!(loaded["data"]["result_label"], "Public");
    refusal(
        host::run(&fixture.arguments(&publication(b"wrong", b"next"), true, true)),
        409,
    );
    refusal(
        host::run(&fixture.arguments(&publication(&first, b""), true, true)),
        400,
    );
    refusal(
        host::run(&fixture.arguments(&publication(b"", &vec![0; 8193]), true, true)),
        413,
    );
    assert_eq!(
        host::run(&fixture.arguments(get, true, false)).expect("preserved")["data"]["output"],
        serde_json::json!(first)
    );
    host::run(&fixture.arguments(&publication(&first, b"next"), true, true)).expect("successor");
    refusal(
        host::run(&fixture.arguments(&publication(&first, b"stale"), true, true)),
        409,
    );
    for input in [
        b"".as_slice(),
        b"AKVR\x02\0\0\0",
        b"AKVR\x01\0\0\0x",
        b"AKVX\x01\0\0\0",
    ] {
        refusal(
            host::run(&fixture.arguments(input, true, true)),
            if input.is_empty() { 400 } else { 422 },
        );
    }
    assert_eq!(
        host::run(&fixture.arguments(get, true, false)).expect("successor preserved")["data"]["output"],
        serde_json::json!(b"next")
    );
}

#[cfg(feature = "solver")]
#[test]
fn storage_host_policy_does_not_change_compiler_labels_or_package_run() {
    let fixture = Fixture::new();
    let mut checked = fixture.compile();
    host::require_storage_profile(&checked).expect("positive control");
    checked.compilation.capability_report.solver_verified = false;
    assert_eq!(
        host::require_storage_profile(&checked)
            .expect_err("live missing witness")
            .downcast_ref::<sigil_compiler::package::PackageError>()
            .expect("gate")
            .code,
        "E_SOLVER_UNVERIFIED"
    );
    let mut checked = fixture.compile();
    let tool = checked
        .compilation
        .typed
        .modules
        .iter_mut()
        .find(|m| m.name == "tool")
        .expect("root");
    tool.functions
        .iter_mut()
        .find(|f| f.export_name == "tool__tool_main")
        .expect("entry")
        .ret_taint = sigil_compiler::ast::TaintLabel::Public;
    assert!(
        host::require_storage_profile(&checked).is_err(),
        "wrong ABI detector"
    );
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["run", "--package"])
        .arg(&fixture.root)
        .args(["--host-profile", "ephemeral", "--json"])
        .output()
        .expect("ordinary CLI");
    assert!(!output.status.success());
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).expect("diagnostics");
    assert_eq!(
        result["diagnostics"]
            .as_array()
            .expect("codes")
            .iter()
            .map(|d| d["code"].as_str().expect("code"))
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([concat!("R", "800")])
    );
    let source = std::fs::read_to_string(fixture.root.join("src/tool.sigil")).expect("source");
    // tool_main already permits Internal values across the host boundary;
    // a local Public binding does not. Exercise that actual language rule.
    let changed = source.replacen("let loaded: i64 @Internal", "let loaded: i64 @Public", 1);
    assert_ne!(changed, source);
    let downgraded = Fixture::with_source(Some(&changed));
    let result = sigil_compiler::package::compile_local_package_with_context(
        &downgraded.root,
        sigil_compiler::CompileOptions::default(),
        &sigil_compiler::CompilerContext::with_host_profile(sigil_runtime::ephemeral_host_profile()),
    );
    let Err(sigil_compiler::package::PackageCompileError::Compiler(error)) = result else {
        panic!("Internal-to-Public binding must fail in compiler");
    };
    assert_eq!(
        error
            .diagnostics()
            .iter()
            .map(|d| d.code().to_string())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([concat!("T", "001").to_owned()])
    );
}

#[cfg(feature = "solver")]
use std::collections::BTreeSet;
