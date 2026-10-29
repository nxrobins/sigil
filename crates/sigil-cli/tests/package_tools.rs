//! Observable lock and execution regressions for real library consumers.
//! The solver lane executes the production runtime; the portable Unix lane
//! checks source selection and solver refusal without claiming execution proof.

#![cfg(unix)]

use sigil_compiler::package::{
    LocalPackageDependency, create_local_package_lock_with_dependencies,
};
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static SEQUENCE: AtomicU64 = AtomicU64::new(0);

struct Project {
    directory: PathBuf,
    root: PathBuf,
    dependency: PathBuf,
    bytes_dependency: Option<PathBuf>,
}

impl Project {
    fn new() -> Self {
        Self::consumer("split-count")
    }

    fn consumer(name: &str) -> Self {
        Self::consumer_with_bytes(name, None)
    }

    fn consumer_with_bytes(name: &str, override_provider: Option<&str>) -> Self {
        let directory = loop {
            let path = std::env::temp_dir().join(format!(
                "sigil-fmt-tools-{}-{}",
                std::process::id(),
                SEQUENCE.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => break path,
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create isolated fixture: {error}"),
            }
        };
        let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let root = directory.join("consumer");
        let dependency = directory.join("formatter");
        let bytes_dependency =
            matches!(name, "edit-distance" | "word-frequency" | "png-dimensions")
                .then(|| directory.join("bytes"));
        let mut copies = vec![
            (repo.join("library/programs").join(name), root.clone()),
            (repo.join("library/packages/fmt"), dependency.clone()),
        ];
        if let Some(bytes) = &bytes_dependency {
            let provider = if matches!(name, "edit-distance" | "word-frequency") {
                "library/packages/bytes/versions/0.1.0-public.5"
            } else if name == "png-dimensions" {
                "library/packages/bytes/versions/0.1.0-public.4"
            } else {
                "library/packages/bytes"
            };
            copies.push((
                repo.join(override_provider.unwrap_or(provider)),
                bytes.clone(),
            ));
        }
        for (source, destination) in copies {
            std::fs::create_dir(&destination).expect("create package root");
            std::fs::create_dir(destination.join("src")).expect("create source directory");
            std::fs::copy(
                source.join("sigil-package.json"),
                destination.join("sigil-package.json"),
            )
            .expect("copy manifest");
            for file in std::fs::read_dir(source.join("src")).expect("list package sources") {
                let file = file.expect("source entry");
                std::fs::copy(file.path(), destination.join("src").join(file.file_name()))
                    .expect("copy source");
            }
        }
        let project = Self {
            directory,
            root,
            dependency,
            bytes_dependency,
        };
        if override_provider.is_some() {
            // Only an explicitly selected compatibility fixture is repinned;
            // ordinary consumers must match their committed declarations.
            let provider = project.bytes_dependency.as_ref().expect("bytes provider");
            let derived = sigil_compiler::package::derive_local_package_lock(provider)
                .expect("derive explicitly selected compatibility version");
            let lock: serde_json::Value = serde_json::from_slice(&derived).expect("provider lock");
            project.edit_manifest(|manifest| {
                let node = &lock["nodes"][0];
                let dep = manifest["dependencies"]
                    .as_array_mut()
                    .expect("dependencies")
                    .iter_mut()
                    .find(|dep| dep["package"] == "sigil/bytes")
                    .expect("bytes declaration");
                dep["requirement"] =
                    serde_json::json!(format!("={}", node["version"].as_str().expect("version")));
                dep["content_hash"] = node["content_hash"].clone();
            });
        }
        project
    }

    fn selections(&self) -> Vec<LocalPackageDependency> {
        let mut selections = vec![LocalPackageDependency {
            package: "sigil/fmt".to_owned(),
            path: self.dependency.clone(),
        }];
        if let Some(bytes) = &self.bytes_dependency {
            selections.push(LocalPackageDependency {
                package: "sigil/bytes".to_owned(),
                path: bytes.clone(),
            });
        }
        selections
    }

    fn lock(&self) -> Vec<u8> {
        create_local_package_lock_with_dependencies(&self.root, &self.selections())
            .expect("derive pinned library lock")
    }

    fn cli(&self, verb: &str, extra: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args([verb, "--package"])
            .arg(&self.root)
            .args(extra)
            .arg("--json")
            .output()
            .expect("invoke package CLI")
    }

    fn edit_manifest(&self, edit: impl FnOnce(&mut serde_json::Value)) {
        let path = self.root.join("sigil-package.json");
        let mut value: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&path).expect("read manifest"))
                .expect("decode manifest");
        edit(&mut value);
        std::fs::write(path, serde_json::to_vec(&value).expect("encode mutation"))
            .expect("write mutation");
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.directory).expect("remove isolated test data");
    }
}

fn envelope(output: &Output) -> serde_json::Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|error| {
        panic!(
            "invalid envelope {error}: stdout={} stderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    })
}

fn cached_source(project: &Project, bytes: &[u8]) -> PathBuf {
    let lock: serde_json::Value = serde_json::from_slice(bytes).expect("decode lock");
    let locator = lock["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .find(|node| node["package"] == "sigil/fmt")
        .expect("fmt node")["source"]["locator"]
        .as_str()
        .expect("locator");
    project.root.join(locator).join("src/fmt.sigil")
}

fn load_graph(
    root: &std::path::Path,
) -> Result<sigil_compiler::package::ResolvedPackageGraph, sigil_compiler::package::PackageError> {
    match sigil_compiler::package::compile_local_package_structural(
        root,
        sigil_compiler::CompileOptions::default(),
    ) {
        Ok(package) => Ok(package.graph),
        Err(sigil_compiler::package::PackageCompileError::Package(error)) => Err(error),
        Err(error) => panic!("fixture must remain structurally compilable: {error}"),
    }
}

fn init_starter(project: &Project, root: &std::path::Path, namespace: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["package-init", "--root"])
        .arg(root)
        .args(["--namespace", namespace])
        .arg("--dependency")
        .arg(format!(
            "sigil/bytes={}",
            project
                .bytes_dependency
                .as_ref()
                .expect("bytes source")
                .display()
        ))
        .arg("--dependency")
        .arg(format!("sigil/fmt={}", project.dependency.display()))
        .arg("--json")
        .output()
        .expect("invoke starter CLI")
}

fn refresh_project() -> Project {
    let project = Project::consumer("png-dimensions");
    let repo =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../library/programs/png-dimensions");
    for name in ["API.md", "README.md", "api-card.json", "tool-inputs.json"] {
        std::fs::copy(repo.join(name), project.root.join(name))
            .expect("copy refresh metadata inputs");
    }
    project.lock();
    project
}

fn refresh_cli(root: &std::path::Path, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["package-refresh", "--root"])
        .arg(root)
        .args(extra)
        .arg("--json")
        .output()
        .expect("invoke explicit root refresh")
}

fn refresh_snapshot(root: &std::path::Path) -> std::collections::BTreeMap<String, Vec<u8>> {
    [
        "API.md",
        "README.md",
        "api-card.json",
        "src/tool.sigil",
        "tool-inputs.json",
        "sigil-package.json",
        "sigil-package.lock.json",
    ]
    .into_iter()
    .map(|name| {
        (
            name.to_owned(),
            std::fs::read(root.join(name)).expect("snapshot refresh files"),
        )
    })
    .collect()
}

// These snapshots are generated application/cache byte contracts, not source
// inspections offered as a proxy for execution. Both graphs are loaded below.
fn tree_bytes(root: &std::path::Path) -> std::collections::BTreeMap<PathBuf, Vec<u8>> {
    fn visit(
        root: &std::path::Path,
        path: &std::path::Path,
        files: &mut std::collections::BTreeMap<PathBuf, Vec<u8>>,
    ) {
        for entry in std::fs::read_dir(path).expect("list owned test materialization") {
            let entry = entry.expect("fixture entry");
            let kind = entry.file_type().expect("fixture entry type");
            if kind.is_dir() {
                visit(root, &entry.path(), files);
            } else {
                assert!(kind.is_file(), "fixture snapshots never follow symlinks");
                files.insert(
                    entry
                        .path()
                        .strip_prefix(root)
                        .expect("descendant")
                        .to_owned(),
                    std::fs::read(entry.path()).expect("snapshot owned fixture file"),
                );
            }
        }
    }
    let mut files = std::collections::BTreeMap::new();
    visit(root, root, &mut files);
    files
}

fn upgraded_starter() -> (Project, PathBuf, PathBuf) {
    let previous = Project::consumer_with_bytes("edit-distance", Some("library/packages/bytes"));
    let next = Project::consumer("png-dimensions");
    let old = previous.directory.join("old-root");
    let candidate = previous.directory.join("candidate");
    for root in [&old, &candidate] {
        assert!(
            init_starter(&previous, root, "upgrade-reader")
                .status
                .success()
        );
    }
    let old_files = tree_bytes(&old);
    assert_eq!(tree_bytes(&candidate), old_files);
    let old_lock = std::fs::read(candidate.join("sigil-package.lock.json")).expect("old lock");
    let next_provider = next.bytes_dependency.as_ref().expect("next provider");
    let identity: serde_json::Value = serde_json::from_slice(
        &sigil_compiler::package::derive_local_package_lock(next_provider)
            .expect("derive explicit upgraded provider identity"),
    )
    .expect("new provider lock");
    let manifest_path = candidate.join("sigil-package.json");
    let mut manifest: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&manifest_path).expect("manifest"))
            .expect("manifest JSON");
    let selected = manifest["dependencies"]
        .as_array_mut()
        .expect("dependencies")
        .iter_mut()
        .find(|dep| dep["package"] == "sigil/bytes")
        .expect("bytes declaration");
    selected["requirement"] = serde_json::json!("=0.1.0-public.4");
    selected["content_hash"] = identity["nodes"][0]["content_hash"].clone();
    std::fs::write(
        &manifest_path,
        serde_json::to_vec_pretty(&manifest).expect("encode"),
    )
    .expect("deliberately select new version and actual content pin");
    let pending = tree_bytes(&candidate);
    let refresh = refresh_cli(&candidate, &[]);
    assert!(!refresh.status.success());
    assert_eq!(
        envelope(&refresh)["diagnostics"][0]["code"],
        concat!("R", "800")
    );
    assert_eq!(tree_bytes(&candidate), pending, "refresh must never repin");
    let mut selections = previous.selections();
    selections
        .iter_mut()
        .find(|dep| dep.package == "sigil/bytes")
        .expect("bytes source")
        .path = next_provider.clone();
    assert_eq!(
        create_local_package_lock_with_dependencies(&candidate, &selections)
            .expect_err("an upgrade cannot overwrite the old lock")
            .code,
        "E_LOCK_CREATE"
    );
    assert_eq!(tree_bytes(&candidate), pending);
    let saved_lock = candidate.join("prior.lock.snapshot");
    assert!(!saved_lock.exists());
    std::fs::rename(candidate.join("sigil-package.lock.json"), &saved_lock)
        .expect("explicitly preserve candidate lock before create-new locking");
    let new_lock = create_local_package_lock_with_dependencies(&candidate, &selections)
        .expect("explicit new selection creates a new graph");
    assert_eq!(std::fs::read(saved_lock).expect("saved old lock"), old_lock);
    let before: serde_json::Value = serde_json::from_slice(&old_lock).expect("old graph");
    let after: serde_json::Value = serde_json::from_slice(&new_lock).expect("new graph");
    let node = |value: &serde_json::Value, package: &str| {
        value["nodes"]
            .as_array()
            .expect("nodes")
            .iter()
            .find(|node| node["package"] == package)
            .expect("selected node")
            .clone()
    };
    assert_eq!(node(&before, "sigil/fmt"), node(&after, "sigil/fmt"));
    assert_eq!(node(&before, "sigil/bytes")["version"], "0.1.0-public.1");
    assert_eq!(node(&after, "sigil/bytes")["version"], "0.1.0-public.4");
    assert_ne!(before["graph_hash"], after["graph_hash"]);
    assert_eq!(
        tree_bytes(&old),
        old_files,
        "rollback root and cache are untouched"
    );
    load_graph(&old).expect("old graph remains valid");
    load_graph(&candidate).expect("new graph is independently valid");
    (previous, old, candidate)
}

#[test]
fn explicit_bytes_upgrade_relocks_without_changing_the_rollback_root() {
    let (_owner, old, candidate) = upgraded_starter();
    let before = tree_bytes(&old);
    assert_ne!(tree_bytes(&candidate), before);
    load_graph(&old).expect("select preserved graph for rollback");
    assert_eq!(tree_bytes(&old), before);
}

#[cfg(feature = "solver")]
#[test]
fn explicit_bytes_upgrade_and_rollback_execute_both_preserved_graphs() {
    let (owner, old, candidate) = upgraded_starter();
    let before = tree_bytes(&old);
    let old_cert = owner.directory.join("old.cert.json");
    let new_cert = owner.directory.join("new.cert.json");
    let old_path = old_cert.to_str().expect("old cert path");
    let new_path = new_cert.to_str().expect("new cert path");
    assert!(
        starter_cli(&old, "check", &["--cert", old_path])
            .status
            .success()
    );
    let certificate = std::fs::read(&old_cert).expect("old certificate");
    let output = starter_cli(&candidate, "run", &["--input", "ABCD", "--cert", old_path]);
    assert!(
        !output.status.success(),
        "old certificate must not authorize an upgrade"
    );
    assert!(
        starter_cli(&candidate, "check", &["--cert", new_path])
            .status
            .success()
    );
    for (root, cert) in [(&old, old_path), (&candidate, new_path)] {
        let output = starter_cli(root, "run", &["--input", "ABCD", "--cert", cert]);
        assert!(output.status.success());
        assert_eq!(envelope(&output)["data"]["output_text"], "1145258561");
        assert!(
            starter_cli(root, "verify-cert", &["--cert", cert])
                .status
                .success()
        );
    }
    assert_eq!(
        std::fs::read(old_cert).expect("old cert preserved"),
        certificate
    );
    assert_eq!(
        tree_bytes(&old),
        before,
        "rollback neither repins nor rewrites"
    );
}

#[cfg(feature = "solver")]
#[test]
fn fresh_starter_uses_big_endian_bytes_then_refreshes_an_edit() {
    let project = Project::consumer("png-dimensions");
    let root = project.directory.join("fresh-project");
    assert!(
        init_starter(&project, &root, "fresh-reader")
            .status
            .success()
    );
    let old = starter_cli(&root, "run", &["--input", "ABCD"]);
    assert!(old.status.success());
    assert_eq!(envelope(&old)["data"]["output_text"], "1145258561");
    let source_path = root.join("src/tool.sigil");
    let source = std::fs::read_to_string(&source_path).expect("generated source");
    std::fs::write(&source_path, source.replace("read_u32_le", "read_u32_be"))
        .expect("newcomer selects the big-endian API");
    let api_path = root.join("API.md");
    let api = std::fs::read_to_string(&api_path).expect("generated API");
    std::fs::write(api_path, api.replace("little-endian", "big-endian"))
        .expect("review and update the application contract");
    assert!(
        !starter_cli(&root, "run", &["--input", "ABCD"])
            .status
            .success()
    );
    assert!(refresh_cli(&root, &[]).status.success());
    let cert = project.directory.join("fresh.cert.json");
    let cert_path = cert.to_str().expect("cert path");
    assert!(
        starter_cli(&root, "check", &["--cert", cert_path])
            .status
            .success()
    );
    let output = starter_cli(&root, "run", &["--input", "ABCD", "--cert", cert_path]);
    assert!(output.status.success());
    assert_eq!(envelope(&output)["data"]["output_text"], "1094861636");
    assert!(
        starter_cli(&root, "verify-cert", &["--cert", cert_path])
            .status
            .success()
    );
}

#[test]
fn refresh_preserves_prior_files_and_dependencies_and_refuses_noop() {
    let project = refresh_project();
    let old_lock: serde_json::Value = serde_json::from_slice(
        &std::fs::read(project.root.join("sigil-package.lock.json")).expect("original lock"),
    )
    .expect("lock JSON");
    let source = project.root.join("src/tool.sigil");
    let text = std::fs::read_to_string(&source).expect("editable source");
    std::fs::write(
        &source,
        text.replace("fmt::decimal_i64(width)", "fmt::decimal_i64(width + 1)"),
    )
    .expect("edit root source");
    std::fs::write(
        project.root.join("API.md"),
        b"# Revised private application contract\n",
    )
    .expect("edit root API");
    let previous = refresh_snapshot(&project.root);
    assert_eq!(
        load_graph(&project.root)
            .expect_err("old lock refuses edited source")
            .code,
        "E_HASH_MISMATCH"
    );
    let output = refresh_cli(&project.root, &[]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let value = envelope(&output);
    assert_eq!(value["command"], "package-refresh");
    assert_eq!(value["data"]["admission"], "not_evaluated");
    let backup = PathBuf::from(
        value["data"]["backup_directory"]
            .as_str()
            .expect("backup path"),
    );
    let receipt: serde_json::Value = serde_json::from_slice(
        &std::fs::read(backup.join("receipt.json")).expect("refresh receipt"),
    )
    .expect("receipt JSON");
    for (name, bytes) in &previous {
        let entry = &receipt["snapshot_files"][name];
        assert_eq!(entry["path"], format!("before/{name}.snapshot"));
        let digest = ring::digest::digest(&ring::digest::SHA256, bytes);
        let hash = format!(
            "sha256:{}",
            digest
                .as_ref()
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>()
        );
        assert_eq!(entry["hash"], hash);
        assert_eq!(
            &std::fs::read(backup.join("before").join(format!("{name}.snapshot")))
                .expect("preserved pre-refresh bytes"),
            bytes
        );
    }
    assert!(backup.join("complete").is_file());
    assert!(!project.root.join(".sigil/refresh.guard").exists());
    let graph = load_graph(&project.root).expect("normal loader accepts refreshed graph");
    assert_eq!(graph.root_package, "png-dimensions/tool");
    let after = refresh_snapshot(&project.root);
    assert_eq!(after["src/tool.sigil"], previous["src/tool.sigil"]);
    assert_eq!(after["API.md"], previous["API.md"]);
    assert_ne!(
        after["sigil-package.lock.json"],
        previous["sigil-package.lock.json"]
    );
    let new_lock: serde_json::Value =
        serde_json::from_slice(&after["sigil-package.lock.json"]).expect("new lock JSON");
    let dependencies = |lock: &serde_json::Value| {
        lock["nodes"]
            .as_array()
            .expect("locked nodes")
            .iter()
            .filter(|node| node["package"] != "png-dimensions/tool")
            .cloned()
            .collect::<Vec<_>>()
    };
    assert_eq!(dependencies(&old_lock), dependencies(&new_lock));
    let noop = refresh_cli(&project.root, &[]);
    assert!(!noop.status.success());
    assert_eq!(refresh_snapshot(&project.root), after);
    assert!(!project.root.join(".sigil/refresh.guard").exists());
}

#[test]
fn refresh_refuses_dependency_declarations_and_cache_changes_without_rewrites() {
    for change in 0..10 {
        let project = refresh_project();
        if change < 7 {
            project.edit_manifest(|manifest| match change {
                0 => {
                    manifest["dependencies"][0]["content_hash"] =
                        serde_json::json!(format!("sha256:{}", "0".repeat(64)))
                }
                1 => {
                    manifest["dependencies"][0]["requirement"] =
                        serde_json::json!(">=0.1.0-public.1")
                }
                2 => manifest["dependencies"][0]["source"] = serde_json::json!("vendored"),
                3 => manifest["dependencies"][0]["default_features"] = serde_json::json!(true),
                4 => {
                    manifest["dependencies"]
                        .as_array_mut()
                        .expect("dependencies")
                        .remove(0);
                }
                5 => manifest["version"] = serde_json::json!("0.1.0-public.2"),
                6 => manifest["dependencies"][0]["package"] = serde_json::json!("other/bytes"),
                _ => unreachable!("only declaration mutations enter this branch"),
            });
        } else {
            let lock: serde_json::Value = serde_json::from_slice(
                &std::fs::read(project.root.join("sigil-package.lock.json")).expect("lock"),
            )
            .expect("lock JSON");
            let locator = lock["nodes"]
                .as_array()
                .expect("nodes")
                .iter()
                .find(|node| node["package"] == "sigil/bytes")
                .expect("bytes node")["source"]["locator"]
                .as_str()
                .expect("cached locator");
            let path = project.root.join(locator).join(if change != 8 {
                "src/bytes.sigil"
            } else {
                "sigil-package.json"
            });
            let mut bytes = std::fs::read(&path).expect("selected dependency bytes");
            bytes.extend_from_slice(if change == 7 {
                b"\n// changed selected bytes\n"
            } else {
                b" "
            });
            // Manifest whitespace has the same canonical hash; change semantic metadata too.
            if change == 8 {
                let mut manifest: serde_json::Value =
                    serde_json::from_slice(&bytes).expect("cached manifest");
                manifest["description"] = serde_json::json!("Changed cached dependency");
                bytes = serde_json::to_vec(&manifest).expect("mutated cached manifest");
            }
            if change == 9 {
                std::fs::remove_file(path).expect("plant missing cached dependency source");
            } else {
                std::fs::write(path, bytes).expect("plant changed cached dependency");
            }
        }
        let before = refresh_snapshot(&project.root);
        let output = refresh_cli(&project.root, &[]);
        assert!(!output.status.success(), "mutation {change}");
        assert_eq!(
            envelope(&output)["diagnostics"][0]["code"],
            concat!("R", "800")
        );
        assert_eq!(refresh_snapshot(&project.root), before);
        assert!(!project.root.join(".sigil/refresh.guard").exists());
    }
}

#[test]
fn refresh_refuses_invalid_prior_lock_and_unsafe_paths_without_overwrites() {
    for change in 0..6 {
        let project = refresh_project();
        let lock_path = project.root.join("sigil-package.lock.json");
        if change < 2 {
            let mut lock: serde_json::Value =
                serde_json::from_slice(&std::fs::read(&lock_path).expect("prior lock"))
                    .expect("lock JSON");
            lock[if change == 0 {
                "graph_hash"
            } else {
                "stdlib_hash"
            }] = serde_json::json!(format!("sha256:{}", "0".repeat(64)));
            std::fs::write(&lock_path, serde_json::to_vec(&lock).expect("corrupt lock"))
                .expect("write invalid prior lock");
        } else if change == 2 {
            std::fs::write(
                project.root.join(".sigil/refresh.guard"),
                b"existing interrupted refresh",
            )
            .expect("existing guard");
        } else if change == 3 {
            std::fs::copy(
                project.root.join("tool-inputs.json"),
                project.root.join("starter-inputs.json"),
            )
            .expect("ambiguous inventories");
        } else {
            let name = if change == 4 {
                "API.md"
            } else {
                "sigil-package.lock.json"
            };
            let saved = project.directory.join("user-owned-file");
            std::fs::rename(project.root.join(name), &saved).expect("preserve user file");
            std::os::unix::fs::symlink(&saved, project.root.join(name))
                .expect("plant leaf symlink");
        }
        let before = refresh_snapshot(&project.root);
        let output = refresh_cli(&project.root, &[]);
        assert!(!output.status.success(), "mutation {change}");
        assert_eq!(refresh_snapshot(&project.root), before);
        if change == 2 {
            assert_eq!(
                std::fs::read(project.root.join(".sigil/refresh.guard")).expect("preserved guard"),
                b"existing interrupted refresh"
            );
        }
        if change >= 4 {
            let name = if change == 4 {
                "API.md"
            } else {
                "sigil-package.lock.json"
            };
            assert!(project.root.join(name).is_symlink());
            assert_eq!(
                std::fs::read(project.directory.join("user-owned-file"))
                    .expect("symlink target unchanged"),
                before[name]
            );
        }
    }
}

#[test]
fn refresh_handles_starter_inventory_and_never_accepts_repin_flags() {
    let project = Project::consumer("word-frequency");
    let root = project.directory.join("fresh-starter");
    assert!(
        init_starter(&project, &root, "fresh-starter")
            .status
            .success()
    );
    let source = root.join("src/tool.sigil");
    let mut bytes = std::fs::read(&source).expect("starter source");
    bytes.extend_from_slice(b"\n// developer edit\n");
    std::fs::write(&source, bytes).expect("edit starter");
    let output = refresh_cli(&root, &[]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(load_graph(&root).is_ok());
    let lock = std::fs::read(root.join("sigil-package.lock.json")).expect("refreshed lock");
    for flags in [
        vec!["--force"],
        vec!["--dependency", "sigil/bytes=elsewhere"],
        vec!["--namespace", "other"],
        vec!["--output-dir", "other"],
    ] {
        let output = refresh_cli(&root, &flags);
        assert_eq!(output.status.code(), Some(2));
        assert_eq!(
            std::fs::read(root.join("sigil-package.lock.json")).expect("lock unchanged"),
            lock
        );
    }
}

#[test]
fn refresh_refuses_malformed_inputs_and_symlinked_journals_without_rewrites() {
    for change in 0..7 {
        let project = refresh_project();
        if change < 4 {
            let bytes: &[u8] = match change {
                0 => b"[]",
                1 => b"null",
                2 => b"{broken",
                _ => b"{}",
            };
            std::fs::write(project.root.join("sigil-package.json"), bytes)
                .expect("malformed manifest witness");
        } else if change == 4 {
            std::fs::write(project.root.join("tool-inputs.json"), b"{}")
                .expect("unbound inventory witness");
        } else if change == 5 {
            std::fs::write(
                project.root.join("src/tool.sigil"),
                b"module tool; pub fn broken(",
            )
            .expect("malformed source witness");
        } else {
            let outside = project.directory.join("user-data");
            std::fs::create_dir(&outside).expect("existing caller directory");
            std::fs::write(outside.join("keep"), b"unchanged").expect("outside sentinel");
            std::os::unix::fs::symlink(&outside, project.root.join(".sigil/refresh"))
                .expect("symlinked journal directory");
            let source = project.root.join("src/tool.sigil");
            let mut bytes = std::fs::read(&source).expect("editable source");
            bytes.extend_from_slice(b"\n// pending edit requires journal creation\n");
            std::fs::write(source, bytes).expect("plant pending edit");
        }
        let before = refresh_snapshot(&project.root);
        let output = refresh_cli(&project.root, &[]);
        assert_eq!(output.status.code(), Some(1), "case {change}");
        assert_eq!(
            envelope(&output)["diagnostics"][0]["code"],
            concat!("R", "800")
        );
        assert_eq!(refresh_snapshot(&project.root), before);
        if change == 6 {
            assert_eq!(
                std::fs::read(project.directory.join("user-data/keep"))
                    .expect("outside data preserved"),
                b"unchanged"
            );
            assert_eq!(
                std::fs::read_dir(project.directory.join("user-data"))
                    .expect("outside directory")
                    .count(),
                1
            );
        }
    }
}

#[test]
fn refresh_serializes_writers_and_preserves_hardlinked_metadata() {
    let project = refresh_project();
    let source = project.root.join("src/tool.sigil");
    let mut bytes = std::fs::read(&source).expect("editable source");
    bytes.extend_from_slice(b"\n// pending edit requires one refresh\n");
    std::fs::write(source, bytes).expect("plant pending edit");
    let previous = refresh_snapshot(&project.root);
    let alias = project.directory.join("previous-manifest-alias");
    std::fs::hard_link(project.root.join("sigil-package.json"), &alias)
        .expect("caller-owned hardlink");
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
    let threads: Vec<_> = (0..2)
        .map(|_| {
            let barrier = barrier.clone();
            let root = project.root.clone();
            std::thread::spawn(move || {
                barrier.wait();
                refresh_cli(&root, &[])
            })
        })
        .collect();
    let outputs: Vec<_> = threads
        .into_iter()
        .map(|thread| thread.join().expect("refresh process finished"))
        .collect();
    assert_eq!(
        outputs
            .iter()
            .filter(|output| output.status.success())
            .count(),
        1
    );
    assert!(load_graph(&project.root).is_ok());
    assert_eq!(
        std::fs::read(alias).expect("hardlinked original preserved"),
        previous["sigil-package.json"]
    );
    let successful = outputs
        .iter()
        .find(|output| output.status.success())
        .expect("one completed refresh");
    let value = envelope(successful);
    let backup = PathBuf::from(value["data"]["backup_directory"].as_str().expect("backup"));
    assert_eq!(
        std::fs::read(backup.join("before/sigil-package.lock.json.snapshot"))
            .expect("old lock preserved"),
        previous["sigil-package.lock.json"]
    );
}

#[cfg(feature = "solver")]
#[test]
fn refreshed_png_runs_edits_and_refuses_old_certificates_and_exhausted_fuel() {
    let project = refresh_project();
    let old_cert = project.directory.join("before.cert.json");
    let new_cert = project.directory.join("after.cert.json");
    let old_path = old_cert.to_str().expect("old cert path");
    let new_path = new_cert.to_str().expect("new cert path");
    assert!(project.cli("check", &["--cert", old_path]).status.success());
    let old_bytes = std::fs::read(&old_cert).expect("original certificate");
    let source = project.root.join("src/tool.sigil");
    let text = std::fs::read_to_string(&source).expect("PNG source");
    std::fs::write(
        &source,
        text.replace("fmt::decimal_i64(width)", "fmt::decimal_i64(width + 1)"),
    )
    .expect("edit PNG output");
    let input = "89504e470d0a1a0a0000000d494844520000032000000258";
    assert!(!project.cli("run", &["--input", input]).status.success());
    assert!(refresh_cli(&project.root, &[]).status.success());
    assert!(
        !project
            .cli("run", &["--input", input, "--cert", old_path])
            .status
            .success()
    );
    assert_eq!(
        std::fs::read(&old_cert).expect("old certificate preserved"),
        old_bytes
    );
    assert!(project.cli("check", &["--cert", new_path]).status.success());
    let output = project.cli("run", &["--input", input, "--cert", new_path]);
    assert!(output.status.success());
    assert_eq!(envelope(&output)["data"]["output_text"], "801x600");
    assert_eq!(envelope(&output)["data"]["admission"], "not_evaluated");
    assert!(
        project
            .cli("verify-cert", &["--cert", new_path])
            .status
            .success()
    );
    let output = project.cli("run", &["--input", input, "--fuel", "1"]);
    assert!(!output.status.success());
    assert_eq!(
        envelope(&output)["diagnostics"][0]["code"],
        concat!("R", "801")
    );
    let output = project.cli("run", &["--input", "bad"]);
    assert!(!output.status.success());
    assert_eq!(
        envelope(&output)["diagnostics"][0]["code"],
        concat!("R", "803")
    );
}

#[cfg(feature = "solver")]
fn starter_cli(root: &std::path::Path, verb: &str, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args([verb, "--package"])
        .arg(root)
        .args(extra)
        .arg("--json")
        .output()
        .expect("invoke generated-project CLI")
}

#[test]
fn starter_creates_a_loadable_graph_and_hashes_real_generated_files() {
    let project = Project::consumer("word-frequency");
    let root = project.directory.join("new header project");
    let output = init_starter(&project, &root, "header-reader");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let value = envelope(&output);
    assert_eq!(value["command"], "package-init");
    assert_eq!(value["data"]["root_package"], "header-reader/tool");
    assert_eq!(value["data"]["admission"], "not_evaluated");
    assert_eq!(value["data"]["locked"], true);
    let graph = load_graph(&root).expect("production loader consumes generated starter");
    assert_eq!(graph.root_package, "header-reader/tool");
    assert_eq!(graph.certificate_nodes.len(), 3);
    let manifest: serde_json::Value = serde_json::from_slice(
        &std::fs::read(root.join("sigil-package.json")).expect("generated manifest"),
    )
    .expect("manifest JSON");
    assert_eq!(manifest["name"], "tool");
    assert_eq!(manifest["modules"], serde_json::json!(["tool"]));
    let inventory: serde_json::Value = serde_json::from_slice(
        &std::fs::read(root.join("starter-inputs.json")).expect("generated inventory"),
    )
    .expect("inventory JSON");
    for (key, file) in [
        ("charter_hash", "README.md"),
        ("api_contract_hash", "API.md"),
        ("api_card_hash", "api-card.json"),
        ("evidence_manifest_hash", "starter-inputs.json"),
    ] {
        let bytes = std::fs::read(root.join(file)).expect("generated file");
        let digest = ring::digest::digest(&ring::digest::SHA256, &bytes);
        let expected = format!(
            "sha256:{}",
            digest
                .as_ref()
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>()
        );
        assert_eq!(manifest["evidence"][key], expected);
    }
    for (file, expected) in inventory["files"].as_object().expect("file inventory") {
        let bytes = std::fs::read(root.join(file)).expect("inventoried file");
        let digest = ring::digest::digest(&ring::digest::SHA256, &bytes);
        assert_eq!(
            expected,
            &format!(
                "sha256:{}",
                digest
                    .as_ref()
                    .iter()
                    .map(|byte| format!("{byte:02x}"))
                    .collect::<String>()
            )
        );
    }
    // SC-P4: actual source tampering must invalidate this fresh locked graph.
    let source = root.join("src/tool.sigil");
    let mut bytes = std::fs::read(&source).expect("generated source");
    bytes.extend_from_slice(b"\n// changed after lock\n");
    std::fs::write(source, bytes).expect("plant changed source");
    assert_eq!(
        load_graph(&root).expect_err("changed source refuses").code,
        "E_HASH_MISMATCH"
    );
}

#[test]
fn starter_never_overwrites_existing_files_directories_or_symlinks() {
    let project = Project::consumer("word-frequency");
    let root = project.directory.join("existing");
    std::fs::create_dir(&root).expect("existing directory");
    let sentinel = root.join("keep");
    std::fs::write(&sentinel, b"user data").expect("sentinel");
    assert!(
        !init_starter(&project, &root, "header-reader")
            .status
            .success()
    );
    assert_eq!(
        std::fs::read(&sentinel).expect("preserved directory"),
        b"user data"
    );
    let file = project.directory.join("existing-file");
    std::fs::write(&file, b"owned file").expect("existing file");
    assert!(
        !init_starter(&project, &file, "header-reader")
            .status
            .success()
    );
    assert_eq!(std::fs::read(&file).expect("preserved file"), b"owned file");
    let link = project.directory.join("existing-link");
    std::os::unix::fs::symlink(&root, &link).expect("destination symlink");
    assert!(
        !init_starter(&project, &link, "header-reader")
            .status
            .success()
    );
    assert_eq!(std::fs::read_link(link).expect("preserved symlink"), root);
    assert_eq!(
        std::fs::read(sentinel).expect("symlink did not redirect writes"),
        b"user data"
    );
}

#[test]
fn starter_rejects_bad_names_and_overlapping_roots_before_creation() {
    let project = Project::consumer("word-frequency");
    for namespace in [
        "",
        "a",
        "Uppercase",
        "../escape",
        "two words",
        "secret\nheader",
    ] {
        let root = project.directory.join("must-not-exist");
        let output = init_starter(&project, &root, namespace);
        assert!(!output.status.success(), "{namespace:?}");
        assert!(!root.exists(), "invalid name must not publish source");
    }
    let root = project
        .bytes_dependency
        .as_ref()
        .expect("bytes source")
        .join("nested-starter");
    assert!(
        !init_starter(&project, &root, "header-reader")
            .status
            .success()
    );
    assert!(!root.exists(), "provider tree must not be changed");
}

#[test]
fn starter_uses_current_source_identity_without_touching_provider_locks() {
    let project = Project::consumer("word-frequency");
    let provider = project.bytes_dependency.as_ref().expect("bytes source");
    let path = provider.join("sigil-package.json");
    let mut manifest: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&path).expect("provider manifest"))
            .expect("manifest JSON");
    manifest["version"] = serde_json::json!("0.1.0-public.2");
    let bytes = serde_json::to_vec(&manifest).expect("serialize selected manifest");
    std::fs::write(&path, &bytes).expect("change explicitly selected provider version");
    let stale_lock = provider.join("sigil-package.lock.json");
    std::fs::write(
        &stale_lock,
        b"old provider lock must not be used or overwritten",
    )
    .expect("stale lock witness");
    let root = project.directory.join("fresh");
    let output = init_starter(&project, &root, "header-reader");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let graph = load_graph(&root).expect("load fresh current-source graph");
    let node = graph
        .certificate_nodes
        .iter()
        .find(|node| node.package == "sigil/bytes")
        .expect("bytes node");
    assert_eq!(node.version, "0.1.0-public.2");
    assert_eq!(std::fs::read(&path).expect("provider preserved"), bytes);
    assert_eq!(
        std::fs::read(stale_lock).expect("stale lock preserved"),
        b"old provider lock must not be used or overwritten"
    );
    let lock = std::fs::read(root.join("sigil-package.lock.json")).expect("new lock");
    assert!(
        !init_starter(&project, &root, "header-reader")
            .status
            .success()
    );
    assert_eq!(
        std::fs::read(root.join("sigil-package.lock.json")).expect("root lock preserved"),
        lock
    );
}

#[test]
fn starter_requires_both_correct_explicit_dependency_sources() {
    let project = Project::consumer("word-frequency");
    let root = project.directory.join("unpublished");
    for selections in [
        vec![],
        vec![format!("sigil/fmt={}", project.dependency.display())],
        vec![
            format!("sigil/fmt={}", project.dependency.display()),
            format!("sigil/bytes={}", project.dependency.display()),
        ],
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_sigil"));
        command.args(["package-init", "--root"]).arg(&root).args([
            "--namespace",
            "header-reader",
            "--json",
        ]);
        for source in selections {
            command.args(["--dependency", &source]);
        }
        let output = command.output().expect("source-selection refusal");
        assert_eq!(output.status.code(), Some(1));
        assert_eq!(
            envelope(&output)["diagnostics"][0]["code"],
            concat!("R", "800")
        );
        assert!(
            !root.exists(),
            "bad sources must refuse before writing project files"
        );
    }
}

#[cfg(not(feature = "solver"))]
#[test]
fn starter_cannot_bypass_the_solver_requirement() {
    let project = Project::consumer("word-frequency");
    let root = project.directory.join("fresh");
    assert!(
        init_starter(&project, &root, "header-reader")
            .status
            .success()
    );
    for verb in ["check", "run"] {
        let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args([verb, "--package"])
            .arg(&root)
            .arg("--json")
            .env("SIGIL_ALLOW_UNVERIFIED_CERT", "1")
            .output()
            .expect("solver refusal");
        assert!(!output.status.success());
        assert_eq!(
            envelope(&output)["diagnostics"][0]["code"],
            concat!("R", "817")
        );
    }
}

#[cfg(feature = "solver")]
#[test]
fn starter_cli_compiles_runs_and_preserves_refusals() {
    let project = Project::consumer("word-frequency");
    let root = project.directory.join("fresh");
    assert!(
        init_starter(&project, &root, "header-reader")
            .status
            .success()
    );
    let cert = project.directory.join("starter.cert.json");
    let cert_path = cert.to_str().expect("temporary path");
    let output = starter_cli(&root, "check", &["--cert", cert_path]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let certificate = std::fs::read(&cert).expect("fresh certificate");
    for (input, expected) in [
        ("ABCD", "1145258561"),
        ("ABCDtail", "1145258561"),
        ("0000", "808464432"),
        ("abcd", "1684234849"),
        ("zzzz", "2054847098"),
    ] {
        let output = starter_cli(&root, "run", &["--cert", cert_path, "--input", input]);
        assert!(output.status.success());
        assert_eq!(envelope(&output)["data"]["output_text"], expected);
        assert_eq!(envelope(&output)["data"]["admission"], "not_evaluated");
        let raw = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["run", "--package"])
            .arg(&root)
            .args(["--input", input])
            .output()
            .expect("raw starter run");
        assert!(raw.status.success());
        assert_eq!(raw.stdout, expected.as_bytes());
    }
    for input in ["", "A", "ABC"] {
        let output = starter_cli(&root, "run", &["--input", input]);
        assert!(!output.status.success());
        assert_eq!(
            envelope(&output)["diagnostics"][0]["code"],
            concat!("R", "803")
        );
    }
    let output = starter_cli(&root, "run", &["--input", "ABCD", "--fuel", "1"]);
    assert!(!output.status.success());
    assert_eq!(
        envelope(&output)["diagnostics"][0]["code"],
        concat!("R", "801")
    );
    assert!(
        starter_cli(&root, "verify-cert", &["--cert", cert_path])
            .status
            .success()
    );
    assert_eq!(
        std::fs::read(cert).expect("certificate preserved"),
        certificate
    );
}

#[test]
fn explicit_sources_derive_a_loadable_graph_and_refuse_lock_overwrite() {
    let project = Project::new();
    let bytes = project.lock();
    let graph = load_graph(&project.root).expect("load graph");
    assert_eq!(graph.root_package, "split-count/tool");
    assert_eq!(graph.certificate_nodes.len(), 2);
    let error = create_local_package_lock_with_dependencies(&project.root, &project.selections())
        .expect_err("existing lock refused");
    assert_eq!(error.code, "E_LOCK_CREATE");
    assert_eq!(
        std::fs::read(project.root.join("sigil-package.lock.json")).expect("read preserved lock"),
        bytes
    );
}

#[test]
fn bracket_consumer_derives_a_loadable_two_node_graph() {
    let project = Project::consumer("bracket-match");
    project.lock();
    let graph = load_graph(&project.root).expect("load bracket graph");
    assert_eq!(graph.root_package, "bracket-match/tool");
    assert_eq!(graph.certificate_nodes.len(), 2);
}

#[test]
fn edit_distance_consumer_derives_a_loadable_three_node_graph() {
    let project = Project::consumer("edit-distance");
    project.lock();
    let graph = load_graph(&project.root).expect("load edit-distance graph");
    assert_eq!(graph.root_package, "edit-distance/tool");
    assert_eq!(graph.certificate_nodes.len(), 3);
    assert_eq!(
        graph
            .certificate_nodes
            .iter()
            .map(|node| node.package.as_str())
            .collect::<std::collections::BTreeSet<_>>(),
        std::collections::BTreeSet::from(["edit-distance/tool", "sigil/bytes", "sigil/fmt"])
    );
}

#[test]
fn word_frequency_consumer_derives_a_loadable_three_node_graph() {
    let project = Project::consumer("word-frequency");
    project.lock();
    let graph = load_graph(&project.root).expect("load word-frequency graph");
    assert_eq!(graph.root_package, "word-frequency/tool");
    assert_eq!(graph.certificate_nodes.len(), 3);
    assert_eq!(
        graph
            .certificate_nodes
            .iter()
            .map(|node| node.package.as_str())
            .collect::<std::collections::BTreeSet<_>>(),
        std::collections::BTreeSet::from(["word-frequency/tool", "sigil/bytes", "sigil/fmt"])
    );
}

#[test]
fn png_consumer_loads_three_nodes_and_binds_actual_application_files() {
    let project = Project::consumer("png-dimensions");
    project.lock();
    let graph = load_graph(&project.root).expect("load fresh PNG consumer");
    assert_eq!(graph.root_package, "png-dimensions/tool");
    assert_eq!(graph.certificate_nodes.len(), 3);
    let repo =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../library/programs/png-dimensions");
    let json = |name: &str| -> serde_json::Value {
        serde_json::from_slice(&std::fs::read(repo.join(name)).expect("application metadata"))
            .expect("valid application JSON")
    };
    let hash = |bytes: &[u8]| {
        format!(
            "sha256:{}",
            ring::digest::digest(&ring::digest::SHA256, bytes)
                .as_ref()
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>()
        )
    };
    let manifest = json("sigil-package.json");
    for (key, name) in [
        ("charter_hash", "README.md"),
        ("api_contract_hash", "API.md"),
        ("api_card_hash", "api-card.json"),
        ("evidence_manifest_hash", "tool-inputs.json"),
    ] {
        assert_eq!(
            manifest["evidence"][key],
            hash(&std::fs::read(repo.join(name)).expect("bound file"))
        );
    }
    for (name, expected) in json("tool-inputs.json")["files"]
        .as_object()
        .expect("input inventory")
    {
        let mut bytes = std::fs::read(repo.join(name)).expect("inventoried file");
        assert_eq!(expected, &hash(&bytes));
        bytes.push(b'!');
        assert_ne!(
            expected,
            &hash(&bytes),
            "changed bytes must break the binding"
        );
    }
    std::fs::write(project.root.join("src/tool.sigil"), b"module tool;\n")
        .expect("plant changed locked source");
    assert_eq!(
        load_graph(&project.root)
            .expect_err("stale application lock refuses")
            .code,
        "E_HASH_MISMATCH"
    );
}

#[test]
fn composition_refuses_missing_changed_and_cached_bytes_without_repinning() {
    let project = Project::consumer("edit-distance");
    let only_fmt = vec![project.selections()[0].clone()];
    assert_eq!(
        create_local_package_lock_with_dependencies(&project.root, &only_fmt)
            .expect_err("bytes source must be explicitly selected")
            .code,
        "E_OFFLINE_MISS"
    );
    let bytes = project.bytes_dependency.as_ref().expect("bytes source");
    let source = bytes.join("src/bytes.sigil");
    let original = std::fs::read(&source).expect("read selected bytes source");
    std::fs::write(&source, b"module bytes;\n").expect("mutate selected source");
    assert_eq!(
        create_local_package_lock_with_dependencies(&project.root, &project.selections())
            .expect_err("changed bytes selection must not silently repin")
            .code,
        "E_HASH_MISMATCH"
    );
    assert!(!project.root.join("sigil-package.lock.json").exists());
    std::fs::write(&source, original).expect("restore selected source");
    let locked = project.lock();
    let lock: serde_json::Value = serde_json::from_slice(&locked).expect("decode composed lock");
    let locator = lock["nodes"]
        .as_array()
        .expect("locked nodes")
        .iter()
        .find(|node| node["package"] == "sigil/bytes")
        .expect("bytes node")["source"]["locator"]
        .as_str()
        .expect("bytes cache locator");
    std::fs::write(
        project.root.join(locator).join("src/bytes.sigil"),
        b"module bytes;\n",
    )
    .expect("mutate pinned bytes cache");
    assert_eq!(
        load_graph(&project.root)
            .expect_err("changed bytes cache must refuse")
            .code,
        "E_HASH_MISMATCH"
    );
    assert_eq!(
        std::fs::read(project.root.join("sigil-package.lock.json")).expect("preserved lock"),
        locked
    );
}

#[cfg(feature = "solver")]
fn compile_project(project: &Project) -> sigil_compiler::package::PackageCompilation {
    project.lock();
    sigil_compiler::package::compile_local_package_with_context(
        &project.root,
        sigil_compiler::CompileOptions::default(),
        &sigil_compiler::CompilerContext::default(),
    )
    .expect("fresh solver compilation of real library graph")
}

#[cfg(feature = "solver")]
fn execute_probe(
    package: &sigil_compiler::package::PackageCompilation,
    input: &[u8],
) -> Result<sigil_runtime::ToolResult, sigil_runtime::ToolError> {
    sigil_runtime::execute_ephemeral_with_budgets(
        &package.compilation.wasm_inner,
        input,
        100_000,
        10_000_000,
        16 * 1024 * 1024,
        &sigil_runtime::IoGrants::none(),
    )
}

#[cfg(feature = "solver")]
fn bytes_probe_source(operation: &str, planted_allocation: bool) -> String {
    let allocation = if planted_allocation {
        "let scratch = alloc(8);"
    } else {
        ""
    };
    format!(
        r#"module tool;
use sigil::bytes;
use sigil::fmt;
pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{
    let before = alloc(0);
    {allocation}
    let status = {operation};
    let after = alloc(0);
    let packed_status = fmt::decimal_i64(status);
    let status_ptr = packed_status / 4294967296;
    let status_len = packed_status - status_ptr * 4294967296;
    let packed_delta = fmt::decimal_i64(after - before);
    let delta_ptr = packed_delta / 4294967296;
    let delta_len = packed_delta - delta_ptr * 4294967296;
    let size = status_len + delta_len + 2 + input_len;
    let out = alloc(size);
    let mut i = 0;
    while i < status_len {{ store8(out+i,load8(status_ptr+i)); i=i+1; }}
    store8(out+status_len,47);
    i=0;
    while i < delta_len {{ store8(out+status_len+1+i,load8(delta_ptr+i)); i=i+1; }}
    store8(out+status_len+1+delta_len,47);
    i=0;
    while i < input_len {{ store8(out+status_len+delta_len+2+i,load8(input_ptr+i)); i=i+1; }}
    return out * 4294967296 + size;
}}"#
    )
}

#[cfg(feature = "solver")]
fn compile_bytes_probe(
    project: &Project,
    operation: &str,
    allocation: bool,
) -> sigil_compiler::package::PackageCompilation {
    std::fs::write(
        project.root.join("src/tool.sigil"),
        bytes_probe_source(operation, allocation),
    )
    .expect("write temporary executable bytes probe");
    compile_project(project)
}

#[cfg(feature = "solver")]
fn repin_mutated_bytes(project: &Project, mutation: impl FnOnce(String) -> String) {
    repin_mutated_bytes_module(project, "bytes", mutation);
}

#[cfg(feature = "solver")]
fn repin_mutated_bytes_module(
    project: &Project,
    module: &str,
    mutation: impl FnOnce(String) -> String,
) {
    let root = project.bytes_dependency.as_ref().expect("bytes selection");
    let path = root.join("src").join(format!("{module}.sigil"));
    let before = std::fs::read_to_string(&path).expect("read bytes mutation input");
    let after = mutation(before.clone());
    assert_ne!(
        before, after,
        "the planted mutation must change executable source"
    );
    std::fs::write(path, after).expect("plant bytes semantic mutation");
    // A mutation is a deliberately selected new dependency, never a bypass of
    // the content check. Derive its actual identity through the production API.
    let derived = sigil_compiler::package::derive_local_package_lock(root)
        .expect("derive mutated dependency identity");
    let lock: serde_json::Value = serde_json::from_slice(&derived).expect("derived lock");
    let hash = lock["nodes"][0]["content_hash"].clone();
    project.edit_manifest(|manifest| {
        for dependency in manifest["dependencies"]
            .as_array_mut()
            .expect("dependencies")
        {
            if dependency["package"] == "sigil/bytes" {
                dependency["content_hash"] = hash.clone();
            }
        }
    });
}

#[cfg(feature = "solver")]
fn output_taint_contracts() -> Vec<String> {
    [
        "bytes_out::append(out:Public,src_ptr:Public,src_len:Public,src_offset:Public,count:Public)->Public",
        "bytes_out::append_output(out:Public,packed:Public)->Public",
        "bytes_out::finish(out:Public)->Public",
        "bytes_out::new(capacity:Public)->Public",
        "bytes_out::push_byte(out:Public,value:Public)->Public",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

#[cfg(feature = "solver")]
fn scan_taint_contracts() -> Vec<String> {
    [
        "bytes_scan::equal(a_ptr:Public,a_len:Public,b_ptr:Public,b_len:Public)->Public",
        "bytes_scan::find_byte(ptr:Public,len:Public,offset:Public,value:Public)->Public",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

#[cfg(feature = "solver")]
fn compile_scan_probe(
    project: &Project,
    operation: &str,
    allocation: bool,
) -> sigil_compiler::package::PackageCompilation {
    let source = bytes_probe_source(operation, allocation).replace(
        "use sigil::bytes;",
        "use sigil::bytes; use sigil::bytes_scan;",
    );
    std::fs::write(project.root.join("src/tool.sigil"), source)
        .expect("write executable raw-byte observation driver");
    compile_project(project)
}

#[cfg(feature = "solver")]
fn python_bytes_reference(requests: &[serde_json::Value]) -> Vec<i64> {
    use std::io::Write;
    use std::process::Stdio;

    // The oracle executes CPython's bytes methods, not a second handwritten
    // version of the SIGIL loops. Only the declared valid-byte domain goes here.
    let script = r#"import json, platform, sys
requests = json.load(sys.stdin)
results = []
for request in requests:
    if request['operation'] == 'find':
        result = bytes(request['bytes']).find(request['value'], request['offset'])
    elif request['operation'] == 'equal':
        result = int(bytes(request['left']) == bytes(request['right']))
    else:
        raise ValueError('unknown reference operation')
    results.append(result)
json.dump({'python': platform.python_version(), 'results': results}, sys.stdout)
"#;
    let mut child = Command::new("python3")
        .args(["-I", "-c", script])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("solver integration setup requires Python 3 for the live bytes oracle");
    {
        let mut input = child.stdin.take().expect("piped oracle input");
        input
            .write_all(&serde_json::to_vec(requests).expect("encode reference requests"))
            .expect("send reference requests");
    }
    let output = child.wait_with_output().expect("wait for bytes oracle");
    assert!(
        output.status.success(),
        "the live reference must execute: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).expect("oracle JSON");
    eprintln!("live Python bytes reference: {}", value["python"]);
    let results = value["results"].as_array().expect("reference results");
    assert_eq!(
        results.len(),
        requests.len(),
        "no missing reference answers"
    );
    results
        .iter()
        .map(|v| v.as_i64().expect("integer reference answer"))
        .collect()
}

#[cfg(feature = "solver")]
#[test]
fn byte_scan_matches_live_python_and_rust_without_memory_or_allocation_changes() {
    let mut requests = Vec::new();
    let mut cases: Vec<(&str, Vec<u8>, i64)> = Vec::new();
    for size in 0..=16 {
        let bytes: Vec<u8> = (0..size).map(|i| [0, 97, 10, 255][i % 4]).collect();
        for offset in 0..=size {
            for value in [0_u8, 1, 10, 97, 255] {
                let expected = bytes[offset..]
                    .iter()
                    .position(|b| *b == value)
                    .map_or(-1, |i| (i + offset) as i64);
                let mut input = u32::from(value).to_le_bytes().to_vec();
                input.extend_from_slice(&(offset as u32).to_le_bytes());
                input.extend_from_slice(&bytes);
                requests.push(serde_json::json!({"operation":"find", "bytes":bytes,
                    "offset":offset, "value":value}));
                cases.push(("find", input, expected));
            }
        }
    }
    let all: Vec<u8> = (0..=255).collect();
    for value in 0..=255_u8 {
        for offset in [0_u32, 128, 256] {
            let expected = all[offset as usize..]
                .iter()
                .position(|b| *b == value)
                .map_or(-1, |i| (i + offset as usize) as i64);
            let mut input = u32::from(value).to_le_bytes().to_vec();
            input.extend_from_slice(&offset.to_le_bytes());
            input.extend_from_slice(&all);
            requests.push(serde_json::json!({"operation":"find", "bytes":all,
                "offset":offset, "value":value}));
            cases.push(("find", input, expected));
        }
    }
    let bytes = [0, 255, 97, 10, 0, 255, 97, 10];
    for a in 0..=bytes.len() {
        for a_len in 0..=bytes.len() - a {
            for b in 0..=bytes.len() {
                for b_len in 0..=bytes.len() - b {
                    let expected = i64::from(bytes[a..a + a_len] == bytes[b..b + b_len]);
                    requests.push(serde_json::json!({"operation":"equal",
                        "left":bytes[a..a+a_len], "right":bytes[b..b+b_len]}));
                    let mut input = vec![a as u8, a_len as u8, b as u8, b_len as u8];
                    input.extend_from_slice(&bytes);
                    cases.push(("equal", input, expected));
                }
            }
        }
    }
    let answers = python_bytes_reference(&requests);
    let project = Project::consumer("word-frequency");
    let find = compile_scan_probe(
        &project,
        "bytes_scan::find_byte(input_ptr+8,input_len-8,bytes::read_u32_le(input_ptr,input_len,4),bytes::read_u32_le(input_ptr,input_len,0))",
        false,
    );
    let project = Project::consumer("word-frequency");
    let equal = compile_scan_probe(
        &project,
        "bytes_scan::equal(input_ptr+4+load8(input_ptr),load8(input_ptr+1),input_ptr+4+load8(input_ptr+2),load8(input_ptr+3))",
        false,
    );
    let facts = &find
        .certificate()
        .packages
        .into_iter()
        .find(|p| p.package == "sigil/bytes")
        .expect("bytes facts");
    assert_eq!(facts.modules, ["bytes", "bytes_out", "bytes_scan"]);
    let mut contracts = vec![
        "bytes::copy_into(dst_ptr:Public,dst_len:Public,dst_offset:Public,src_ptr:Public,src_len:Public,src_offset:Public,count:Public)->Public".to_owned(),
        "bytes::read_u32_be(ptr:Public,len:Public,offset:Public)->Public".to_owned(),
        "bytes::read_u32_le(ptr:Public,len:Public,offset:Public)->Public".to_owned(),
        "bytes::write_u32_le(ptr:Public,len:Public,offset:Public,value:Public)->Public".to_owned(),
    ];
    contracts.extend(output_taint_contracts());
    contracts.extend(scan_taint_contracts());
    assert_eq!(facts.derived.taint_contracts, contracts);
    assert_eq!(facts.derived.effects, ["Alloc"]);
    assert_eq!(facts.derived.rings, ["inner"]);
    assert!(facts.derived.host_imports.is_empty());
    assert!(facts.derived.grant_categories.is_empty());
    assert!(facts.derived.trusted_surface.is_empty());
    let mut max_find = 0;
    let mut max_equal = 0;
    for ((operation, input, expected), python) in cases.iter().zip(answers) {
        assert_eq!(*expected, python, "Rust and Python reference disagreement");
        let package = if *operation == "find" { &find } else { &equal };
        let result = execute_probe(package, input).expect("valid raw-byte views");
        let mut expected_output = format!("{expected}/0/").into_bytes();
        expected_output.extend(input);
        assert_eq!(
            result.output, expected_output,
            "{operation} input={input:?}"
        );
        if *operation == "find" {
            max_find = max_find.max(result.fuel_consumed);
        } else {
            max_equal = max_equal.max(result.fuel_consumed);
        }
    }
    eprintln!(
        "byte reader observations: {} live-reference cases; whole-driver maxima find={max_find}, equal={max_equal}",
        cases.len()
    );
    assert_eq!(
        cases.len(),
        3558,
        "the measured reference grid stays complete"
    );
    assert!(max_find <= 542, "measured find whole-driver ceiling");
    assert!(max_equal <= 35, "measured equality whole-driver ceiling");
    for size in [16, 255, 1024] {
        let mut input = vec![97; size];
        input[size - 1] = 255;
        let answers = python_bytes_reference(&[
            serde_json::json!({"operation":"find","bytes":input,"offset":0,"value":255}),
            serde_json::json!({"operation":"equal","left":input,"right":input}),
        ]);
        assert_eq!(answers, [(size - 1) as i64, 1]);
        for (operation, status) in [
            ("find_byte(input_ptr,input_len,0,255)", (size - 1) as i64),
            ("equal(input_ptr,input_len,input_ptr,input_len)", 1),
        ] {
            let project = Project::consumer("word-frequency");
            let package = compile_scan_probe(&project, &format!("bytes_scan::{operation}"), false);
            let result = execute_probe(&package, &input).expect("larger raw-byte view");
            let mut expected = format!("{status}/0/").into_bytes();
            expected.extend(&input);
            assert_eq!(result.output, expected);
            eprintln!(
                "byte reader larger view: {size} bytes, {operation}, {} whole-driver SIGIL fuel",
                result.fuel_consumed
            );
        }
    }
    // SC-P4: a planted allocation and an input write must be observable.
    let control = Project::consumer("word-frequency");
    let package = compile_scan_probe(
        &control,
        "bytes_scan::find_byte(input_ptr,input_len,0,90)",
        true,
    );
    assert_eq!(
        execute_probe(&package, b"Zbcd")
            .expect("allocation control")
            .output,
        b"0/8/Zbcd"
    );
    let control = Project::consumer("word-frequency");
    repin_mutated_bytes_module(&control, "bytes_scan", |source| {
        source.replace(
            "    let mut i = offset;",
            "    store8(ptr,90);\n    let mut i = offset;",
        )
    });
    let package = compile_scan_probe(
        &control,
        "bytes_scan::find_byte(input_ptr,input_len,0,90)",
        false,
    );
    assert_eq!(
        execute_probe(&package, b"abcd")
            .expect("input write control")
            .output,
        b"0/0/Zbcd"
    );
}

#[cfg(feature = "solver")]
#[test]
fn byte_scan_scalar_errors_and_empty_views_refuse_before_access() {
    for (operation, status) in [
        ("find_byte(-1,0,0,256)", -400),
        ("find_byte(0,-1,0,256)", -400),
        ("find_byte(0,0,-1,256)", -400),
        ("find_byte(0,0,1,256)", -413),
        ("find_byte(2147483648,0,0,256)", -413),
        ("find_byte(2147483647,1,0,256)", -413),
        ("find_byte(0,9223372036854775807,0,256)", -413),
        ("find_byte(0,0,0,-1)", -422),
        ("find_byte(0,0,0,256)", -422),
        ("find_byte(2147483647,0,0,255)", -1),
        ("find_byte(2000000000,10,10,255)", -1),
        ("find_byte(input_ptr,input_len,0,255)", -1),
        ("equal(-1,0,0,0)", -400),
        ("equal(0,-1,0,0)", -400),
        ("equal(0,0,-1,0)", -400),
        ("equal(0,0,0,-1)", -400),
        ("equal(2147483648,0,0,1)", -413),
        ("equal(2147483647,1,0,0)", -413),
        ("equal(0,0,2147483647,1)", -413),
        ("equal(0,9223372036854775807,0,0)", -413),
        ("equal(2147483647,0,2147483647,0)", 1),
        ("equal(2000000000,1,2000000000,0)", 0),
        ("equal(input_ptr,4,input_ptr+1,3)", 0),
        ("equal(input_ptr,4,input_ptr,4)", 1),
        ("equal(0,0,0,(-9223372036854775807-1))", -400),
    ] {
        let project = Project::consumer("word-frequency");
        let package = compile_scan_probe(&project, &format!("bytes_scan::{operation}"), false);
        let result = execute_probe(&package, b"abcd").expect("scalar checks precede memory access");
        assert_eq!(
            result.output,
            format!("{status}/0/abcd").as_bytes(),
            "{operation}"
        );
    }
}

#[cfg(feature = "solver")]
#[test]
fn byte_scan_mutants_labels_and_consumer_error_paths_are_checked() {
    for (needle, replacement, call, input, expected) in [
        (
            "return i;",
            "return i + 1;",
            "find_byte(input_ptr,input_len,0,97)",
            b"abca".as_slice(),
            b"0/0/abca".as_slice(),
        ),
        (
            "    return -1;",
            "    return 0;",
            "find_byte(input_ptr,input_len,0,255)",
            b"abcd",
            b"-1/0/abcd",
        ),
        (
            "if a_len != b_len { return 0; }",
            "if a_len != b_len { return 1; }",
            "equal(input_ptr,4,input_ptr,3)",
            b"abcd",
            b"0/0/abcd",
        ),
        (
            "!= load8(b_ptr + i)",
            "== load8(b_ptr + i)",
            "equal(input_ptr,4,input_ptr,4)",
            b"abcd",
            b"1/0/abcd",
        ),
    ] {
        let project = Project::consumer("word-frequency");
        repin_mutated_bytes_module(&project, "bytes_scan", |source| {
            source.replace(needle, replacement)
        });
        let package = compile_scan_probe(&project, &format!("bytes_scan::{call}"), false);
        assert_ne!(
            execute_probe(&package, input)
                .expect("executable mutation")
                .output,
            expected,
            "must kill {needle}"
        );
    }
    for operation in ["find_byte", "equal"] {
        for position in 0..4 {
            for label in ["Public", "Internal", "Secret"] {
                let mut args = ["0"; 4];
                args[position] = "value";
                let project = Project::consumer("word-frequency");
                let source = format!(
                    "module tool; use sigil::bytes_scan; use sigil::fmt; fn sample(value:i64 @{label})->i64 @{label} {{return bytes_scan::{operation}({});}} pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return fmt::decimal_i64(0);}}",
                    args.join(",")
                );
                std::fs::write(project.root.join("src/tool.sigil"), source)
                    .expect("write labeled reader caller");
                project.lock();
                let result = project.cli("check", &[]);
                if label == "Public" {
                    assert!(result.status.success(), "Public accept twin");
                } else {
                    assert!(
                        !result.status.success(),
                        "confidential argument must refuse"
                    );
                    let value = envelope(&result);
                    let codes = value["diagnostics"]
                        .as_array()
                        .expect("diagnostics")
                        .iter()
                        .map(|d| d["code"].as_str().expect("code"))
                        .collect::<std::collections::BTreeSet<_>>();
                    assert_eq!(
                        codes,
                        std::collections::BTreeSet::from([concat!("T", "001")])
                    );
                }
            }
        }
    }
    for (consumer, signature, input) in [
        (
            "edit-distance",
            "pub fn find_byte(ptr: i64, len: i64, offset: i64, value: i64) -> i64 {",
            b"kitten\nsitting".as_slice(),
        ),
        (
            "word-frequency",
            "pub fn equal(a_ptr: i64, a_len: i64, b_ptr: i64, b_len: i64) -> i64 {",
            b"red blue red".as_slice(),
        ),
    ] {
        let project = Project::consumer(consumer);
        repin_mutated_bytes_module(&project, "bytes_scan", |source| {
            source.replace(signature, &format!("{signature} return -413;"))
        });
        let package = compile_project(&project);
        assert!(
            matches!(
                execute_probe(&package, input),
                Err(sigil_runtime::ToolError::Trapped { .. })
            ),
            "{consumer} must refuse reader errors instead of publishing data"
        );
    }
    for site in ["prev_end - prev_start);", "scan_end - scan_start);"] {
        let project = Project::consumer("word-frequency");
        let path = project.root.join("src/tool.sigil");
        let before = std::fs::read_to_string(&path).expect("read comparison call sites");
        let after = before.replace(site, "-1);");
        assert_ne!(after, before, "the selected call site must change");
        std::fs::write(path, after).expect("supply an invalid view at exactly one comparison site");
        let package = compile_project(&project);
        assert!(
            matches!(
                execute_probe(&package, b"red blue red"),
                Err(sigil_runtime::ToolError::Trapped { .. })
            ),
            "the library error from {site} must refuse, not become equality data"
        );
    }
}

#[cfg(feature = "solver")]
#[test]
fn byte_scan_upgrade_keeps_previous_roots_and_certificates_usable() {
    for previous_provider in [
        "library/packages/bytes",
        "library/packages/bytes/versions/0.1.0-public.4",
    ] {
        let previous = Project::consumer_with_bytes("edit-distance", Some(previous_provider));
        let next = Project::consumer("word-frequency");
        let old = previous.directory.join("reader-before");
        let candidate = previous.directory.join("reader-next");
        for root in [&old, &candidate] {
            assert!(
                init_starter(&previous, root, "scan-reader")
                    .status
                    .success()
            );
        }
        let old_cert = previous.directory.join("before.cert.json");
        let old_path = old_cert.to_str().expect("cert path");
        assert!(
            starter_cli(&old, "check", &["--cert", old_path])
                .status
                .success()
        );
        let old_files = tree_bytes(&old);
        let old_cert_bytes = std::fs::read(&old_cert).expect("old cert bytes");
        let manifest_path = candidate.join("sigil-package.json");
        let mut manifest: serde_json::Value =
            serde_json::from_slice(&std::fs::read(&manifest_path).expect("manifest"))
                .expect("JSON");
        let provider = next.bytes_dependency.as_ref().expect("new bytes");
        let identity: serde_json::Value = serde_json::from_slice(
            &sigil_compiler::package::derive_local_package_lock(provider).expect("new identity"),
        )
        .expect("JSON");
        let dep = manifest["dependencies"]
            .as_array_mut()
            .expect("deps")
            .iter_mut()
            .find(|d| d["package"] == "sigil/bytes")
            .expect("bytes dep");
        dep["requirement"] = serde_json::json!("=0.1.0-public.5");
        dep["content_hash"] = identity["nodes"][0]["content_hash"].clone();
        std::fs::write(&manifest_path, serde_json::to_vec(&manifest).expect("JSON"))
            .expect("explicit selection");
        let pending = tree_bytes(&candidate);
        assert!(!refresh_cli(&candidate, &[]).status.success());
        assert_eq!(
            tree_bytes(&candidate),
            pending,
            "refresh cannot repin dependencies"
        );
        let mut selections = previous.selections();
        selections
            .iter_mut()
            .find(|d| d.package == "sigil/bytes")
            .expect("bytes")
            .path = provider.clone();
        assert_eq!(
            create_local_package_lock_with_dependencies(&candidate, &selections)
                .expect_err("old lock cannot be overwritten")
                .code,
            "E_LOCK_CREATE"
        );
        let old_lock =
            std::fs::read(candidate.join("sigil-package.lock.json")).expect("old candidate lock");
        let saved = candidate.join("before.lock.snapshot");
        std::fs::rename(candidate.join("sigil-package.lock.json"), &saved)
            .expect("preserve previous lock");
        let new_lock = create_local_package_lock_with_dependencies(&candidate, &selections)
            .expect("explicit new lock");
        assert_eq!(std::fs::read(saved).expect("preserved lock"), old_lock);
        let node = |raw: &[u8], package: &str| {
            let value: serde_json::Value = serde_json::from_slice(raw).expect("lock JSON");
            value["nodes"]
                .as_array()
                .expect("nodes")
                .iter()
                .find(|n| n["package"] == package)
                .expect("node")
                .clone()
        };
        assert_eq!(node(&old_lock, "sigil/fmt"), node(&new_lock, "sigil/fmt"));
        assert_eq!(node(&new_lock, "sigil/bytes")["version"], "0.1.0-public.5");
        let before_edit = previous.directory.join("before-edit.cert.json");
        let before_path = before_edit.to_str().expect("cert path");
        assert!(
            starter_cli(&candidate, "check", &["--cert", before_path])
                .status
                .success()
        );
        let before_bytes = std::fs::read(&before_edit).expect("before edit cert");
        std::fs::write(
            candidate.join("src/tool.sigil"),
            r#"module tool;
use sigil::bytes; use sigil::bytes_scan; use sigil::fmt;
pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {Alloc} {
    let found=bytes_scan::find_byte(input_ptr,input_len,0,65);
    if found < -1 {return found;} else {}
    let compared=bytes_scan::equal(input_ptr,input_len,input_ptr,input_len);
    if compared < 0 {return compared;} else {}
    let value=bytes::read_u32_le(input_ptr,input_len,0);
    if value < 0 {return value;} else {}
    return fmt::decimal_i64(value);
}"#,
        )
        .expect("edit new reader");
        assert!(
            !starter_cli(&candidate, "run", &["--input", "ABCD"])
                .status
                .success()
        );
        assert!(refresh_cli(&candidate, &[]).status.success());
        for stale in [old_path, before_path] {
            assert!(
                !starter_cli(&candidate, "run", &["--input", "ABCD", "--cert", stale])
                    .status
                    .success()
            );
        }
        let next_cert = previous.directory.join("next.cert.json");
        let next_path = next_cert.to_str().expect("cert path");
        assert!(
            starter_cli(&candidate, "check", &["--cert", next_path])
                .status
                .success()
        );
        for (root, cert) in [(&old, old_path), (&candidate, next_path)] {
            let result = starter_cli(root, "run", &["--input", "ABCD", "--cert", cert]);
            assert!(result.status.success());
            assert_eq!(envelope(&result)["data"]["output_text"], "1145258561");
            assert!(
                starter_cli(root, "verify-cert", &["--cert", cert])
                    .status
                    .success()
            );
        }
        assert!(
            !starter_cli(&candidate, "run", &["--input", "ABC"])
                .status
                .success()
        );
        assert!(
            !starter_cli(&candidate, "run", &["--input", "ABCD", "--fuel", "1"])
                .status
                .success()
        );
        assert_eq!(
            tree_bytes(&old),
            old_files,
            "rollback root/lock/cache remain unchanged"
        );
        assert_eq!(std::fs::read(old_cert).expect("old cert"), old_cert_bytes);
        assert_eq!(
            std::fs::read(before_edit).expect("pre-edit cert"),
            before_bytes
        );
        let locked =
            std::fs::read(candidate.join("sigil-package.lock.json")).expect("new root lock");
        let bytes = node(&locked, "sigil/bytes");
        let locator = bytes["source"]["locator"].as_str().expect("cache locator");
        std::fs::write(
            candidate.join(locator).join("src/bytes_scan.sigil"),
            "module bytes_scan;\n",
        )
        .expect("plant changed cached reader");
        assert_eq!(
            load_graph(&candidate)
                .expect_err("changed cached reader refuses")
                .code,
            "E_HASH_MISMATCH"
        );
        assert_eq!(
            std::fs::read(candidate.join("sigil-package.lock.json")).expect("lock intact"),
            locked
        );
    }
}

#[cfg(feature = "solver")]
fn compile_output_probe(
    project: &Project,
    capacity: &str,
    setup: &str,
    operations: &str,
    planted_allocation: bool,
) -> sigil_compiler::package::PackageCompilation {
    let allocation = if planted_allocation {
        "let scratch = alloc(8);"
    } else {
        ""
    };
    let source = format!(
        r#"module tool;
use sigil::bytes;
use sigil::bytes_out;
use sigil::fmt;
fn emit_number(ptr:i64,offset:i64,value:i64)->i64 ! {{Alloc}} {{
    let text = fmt::decimal_i64(value);
    let source = text / 4294967296;
    let count = text - source * 4294967296;
    let mut i = 0;
    while i < count {{ store8(ptr+offset+i,load8(source+i)); i=i+1; }}
    store8(ptr+offset+count,47);
    return offset+count+1;
}}
pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{
    let origin = alloc(0);
    let out = bytes_out::new({capacity});
    let constructed = alloc(0);
    let observed_ptr = out.ptr;
    let observed_capacity = out.capacity;
    let mut i = 0;
    while i < observed_capacity {{ store8(observed_ptr+i,204); i=i+1; }}
    {setup}
    let before = alloc(0);
    {allocation}
    {operations}
    let packed = bytes_out::finish(out);
    let after = alloc(0);
    let mut status = packed;
    if packed >= 0 {{
        let pointer = packed / 4294967296;
        status = packed - pointer * 4294967296;
        if pointer != out.ptr {{ return -499; }} else {{}}
    }} else {{}}
    let result = alloc(192+observed_capacity+input_len);
    let mut offset = emit_number(result,0,status);
    offset = emit_number(result,offset,out.length);
    offset = emit_number(result,offset,out.error);
    offset = emit_number(result,offset,constructed-origin);
    offset = emit_number(result,offset,after-before);
    i=0;
    while i < observed_capacity {{ store8(result+offset,load8(observed_ptr+i)); offset=offset+1; i=i+1; }}
    store8(result+offset,47); offset=offset+1;
    i=0;
    while i < input_len {{ store8(result+offset,load8(input_ptr+i)); offset=offset+1; i=i+1; }}
    return result*4294967296+offset;
}}"#
    );
    std::fs::write(project.root.join("src/tool.sigil"), source)
        .expect("write executable builder observation driver");
    compile_project(project)
}

#[cfg(feature = "solver")]
fn output_observation(
    status: i64,
    length: i64,
    error: i64,
    construction: i64,
    growth: i64,
    memory: &[u8],
    input: &[u8],
) -> Vec<u8> {
    let mut bytes = format!("{status}/{length}/{error}/{construction}/{growth}/").into_bytes();
    bytes.extend_from_slice(memory);
    bytes.push(b'/');
    bytes.extend_from_slice(input);
    bytes
}

#[cfg(feature = "solver")]
#[test]
fn output_builder_bounds_errors_memory_and_allocation_are_observable() {
    // Complete byte output exposes prefix retention, field mutation and input writes.
    for (capacity, setup, operations, status, length, error, memory) in [
        ("0", "", "", 0, 0, 0, b"".as_slice()),
        (
            "-1",
            "",
            "bytes_out::push_byte(out,65);",
            -400,
            0,
            -400,
            b"",
        ),
        (
            "2147483648",
            "",
            "bytes_out::append(out,9223372036854775807,1,0,1);",
            -413,
            0,
            -413,
            b"",
        ),
        (
            "0",
            "",
            "bytes_out::append(out,9223372036854775807,0,0,0);",
            0,
            0,
            0,
            b"",
        ),
        ("0", "", "bytes_out::push_byte(out,-1);", -413, 0, -413, b""),
        ("(-9223372036854775807-1)", "", "", -400, 0, -400, b""),
        (
            "4",
            "bytes_out::append(out,input_ptr,4,0,4);",
            "bytes_out::append(out,9223372036854775807,0,0,0);",
            4,
            4,
            0,
            b"abcd",
        ),
        (
            "4",
            "",
            "bytes_out::append_output(out,9223372036854775807);",
            -413,
            0,
            -413,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::append_output(out,(-9223372036854775807-1)); bytes_out::push_byte(out,65);",
            i64::MIN,
            0,
            i64::MIN,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::append(out,input_ptr,4,0,4);",
            4,
            4,
            0,
            b"abcd",
        ),
        (
            "4",
            "",
            "bytes_out::append_output(out,input_ptr*4294967296+4);",
            4,
            4,
            0,
            b"abcd",
        ),
        (
            "4",
            "",
            "bytes_out::push_byte(out,255);",
            1,
            1,
            0,
            b"\xff\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::push_byte(out,256);",
            -422,
            0,
            -422,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::push_byte(out,-1);",
            -422,
            0,
            -422,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::append(out,9223372036854775807,4,0,5);",
            -413,
            0,
            -413,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::append(out,9223372036854775807,-1,0,0);",
            -400,
            0,
            -400,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::append(out,input_ptr,4,-1,1);",
            -400,
            0,
            -400,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::append(out,input_ptr,4,9223372036854775807,-1);",
            -400,
            0,
            -400,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::append(out,input_ptr,9223372036854775807,9223372036854775807,1);",
            -413,
            0,
            -413,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "",
            "bytes_out::append_output(out,-777); bytes_out::push_byte(out,65);",
            -777,
            0,
            -777,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "bytes_out::push_byte(out,88);",
            "bytes_out::append(out,input_ptr,4,0,4); bytes_out::push_byte(out,89); bytes_out::append_output(out,-777);",
            -413,
            1,
            -413,
            b"X\xcc\xcc\xcc",
        ),
        (
            "4",
            "out.length=-1;",
            "bytes_out::push_byte(out,65);",
            -400,
            -1,
            -400,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "4",
            "out.length=5;",
            "bytes_out::append(out,input_ptr,4,0,1);",
            -413,
            5,
            -413,
            b"\xcc\xcc\xcc\xcc",
        ),
        (
            "6",
            "bytes_out::append(out,input_ptr,4,0,3);",
            "bytes_out::append(out,out.ptr,6,1,3);",
            6,
            6,
            0,
            b"abcbc\xcc",
        ),
    ] {
        let project = Project::consumer("png-dimensions");
        let package = compile_output_probe(&project, capacity, setup, operations, false);
        let result = execute_probe(&package, b"abcd").expect("bounded builder operation");
        assert_eq!(
            result.output,
            output_observation(
                status,
                length,
                error,
                memory.len() as i64 + 32,
                0,
                memory,
                b"abcd"
            ),
            "capacity={capacity}; {setup}; {operations}"
        );
    }
    let project = Project::consumer("png-dimensions");
    let package = compile_output_probe(
        &project,
        "load8(input_ptr)",
        "",
        "bytes_out::append(out,input_ptr+4,8,load8(input_ptr+1),load8(input_ptr+2));",
        false,
    );
    let mut max_fuel = 0;
    for capacity in 0..=8_u8 {
        for offset in 0..=9_u8 {
            for count in 0..=9_u8 {
                let input = [
                    capacity, offset, count, 0xa5, b'a', b'b', b'c', b'd', b'e', b'f', b'g', b'h',
                    0x5a,
                ];
                let valid = offset <= 8 && count <= 8 - offset && count <= capacity;
                let mut memory = vec![0xcc; usize::from(capacity)];
                if valid {
                    memory[..usize::from(count)].copy_from_slice(
                        &input[4 + usize::from(offset)..4 + usize::from(offset + count)],
                    );
                }
                let status = if valid { i64::from(count) } else { -413 };
                let length = if valid { i64::from(count) } else { 0 };
                let error = if valid { 0 } else { -413 };
                let result = execute_probe(&package, &input).expect("generated builder range");
                assert_eq!(
                    result.output,
                    output_observation(
                        status,
                        length,
                        error,
                        i64::from(capacity) + 32,
                        0,
                        &memory,
                        &input
                    ),
                    "capacity={capacity} offset={offset} count={count}"
                );
                max_fuel = max_fuel.max(result.fuel_consumed);
            }
        }
    }
    eprintln!(
        "builder observations: 900 generated ranges; maximum {max_fuel} whole-driver SIGIL fuel"
    );
    assert!(
        max_fuel <= 91,
        "the measured small-range driver fuel ceiling must not grow"
    );
    for count in [16, 255, 1024] {
        let project = Project::consumer("png-dimensions");
        let package = compile_output_probe(
            &project,
            &count.to_string(),
            "",
            "bytes_out::append(out,input_ptr,input_len,0,input_len);",
            false,
        );
        let input = (0..count).map(|i| (i % 256) as u8).collect::<Vec<_>>();
        let result = execute_probe(&package, &input).expect("larger bounded builder append");
        assert_eq!(
            result.output,
            output_observation(count, count, 0, count + 32, 0, &input, &input)
        );
        eprintln!(
            "builder large append: {count} bytes; {} whole-driver SIGIL fuel",
            result.fuel_consumed
        );
    }
    // SC-P4: the observer must report planted growth and an external memory write.
    let control = Project::consumer("png-dimensions");
    let package = compile_output_probe(
        &control,
        "4",
        "",
        "store8(input_ptr,90); bytes_out::push_byte(out,65);",
        true,
    );
    assert_eq!(
        execute_probe(&package, b"abcd")
            .expect("live observer controls")
            .output,
        output_observation(1, 1, 0, 36, 8, b"A\xcc\xcc\xcc", b"Zbcd")
    );
}

#[cfg(feature = "solver")]
#[test]
fn output_builder_mutations_and_confidential_inputs_are_rejected() {
    for (needle, replacement, capacity, setup, operations, expected) in [
        (
            "if out.error < 0 { return out.error; } else {}",
            "if false { return out.error; } else {}",
            "4",
            "bytes_out::push_byte(out,88);",
            "bytes_out::append(out,input_ptr,4,0,4); bytes_out::push_byte(out,89);",
            output_observation(-413, 1, -413, 36, 0, b"X\xcc\xcc\xcc", b"abcd"),
        ),
        (
            "    if checked < 0 { return checked; } else {}",
            "    if false { return checked; } else {}",
            "1",
            "bytes_out::push_byte(out,65);",
            "bytes_out::push_byte(out,66);",
            output_observation(-413, 1, -413, 33, 0, b"A", b"abcd"),
        ),
        (
            "    out.length = copied;",
            "    out.length = out.length;",
            "4",
            "",
            "bytes_out::append(out,input_ptr,4,0,4);",
            output_observation(4, 4, 0, 36, 0, b"abcd", b"abcd"),
        ),
        (
            "    if value < 0 || value > 255 {",
            "    store8(out.ptr + out.length, 0);\n    if value < 0 || value > 255 {",
            "4",
            "",
            "bytes_out::push_byte(out,256);",
            output_observation(-422, 0, -422, 36, 0, b"\xcc\xcc\xcc\xcc", b"abcd"),
        ),
    ] {
        let project = Project::consumer("png-dimensions");
        repin_mutated_bytes_module(&project, "bytes_out", |text| {
            text.replace(needle, replacement)
        });
        let package = compile_output_probe(&project, capacity, setup, operations, false);
        let observed = execute_probe(&package, b"abcd").expect("live builder mutation");
        assert_ne!(
            observed.output, expected,
            "memory/length/error observer must kill {needle}"
        );
    }
    let mut samples = vec![
        "let out = bytes_out::new(value); return bytes_out::finish(out);".to_owned(),
        "let out = bytes_out::new(8); return bytes_out::append_output(out,value);".to_owned(),
        "let out = bytes_out::new(8); return bytes_out::push_byte(out,value);".to_owned(),
    ];
    for argument in 0..4 {
        let mut args = ["0"; 4];
        args[argument] = "value";
        samples.push(format!(
            "let out = bytes_out::new(8); return bytes_out::append(out,{});",
            args.join(",")
        ));
    }
    for label in ["Public", "Internal", "Secret"] {
        let mut functions: Vec<String> = samples
            .iter()
            .map(|body| {
                format!("fn sample(value:i64 @{label})->i64 @{label} ! {{Alloc}} {{{body}}}")
            })
            .collect();
        for operation in [
            "append(out,0,0,0,0)",
            "append_output(out,0)",
            "push_byte(out,65)",
            "finish(out)",
        ] {
            functions.push(format!("fn sample(out:Builder @{label} @Mut)->i64 @{label} {{return bytes_out::{operation};}}"));
        }
        for sample in functions {
            let project = Project::consumer("png-dimensions");
            let source = format!(
                "module tool; use sigil::bytes; use sigil::bytes_out; use sigil::fmt; {sample} pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return fmt::decimal_i64(0);}}"
            );
            std::fs::write(project.root.join("src/tool.sigil"), source)
                .expect("write labeled builder caller");
            project.lock();
            let result = project.cli("check", &[]);
            if label == "Public" {
                assert!(
                    result.status.success(),
                    "Public accept twin: {sample}: {}",
                    String::from_utf8_lossy(&result.stdout)
                );
            } else {
                assert!(
                    !result.status.success(),
                    "confidential builder argument must refuse"
                );
                let value = envelope(&result);
                let codes = value["diagnostics"]
                    .as_array()
                    .expect("diagnostics")
                    .iter()
                    .map(|d| d["code"].as_str().expect("code"))
                    .collect::<std::collections::BTreeSet<_>>();
                assert_eq!(
                    codes,
                    std::collections::BTreeSet::from([concat!("T", "001")]),
                    "{sample}"
                );
            }
        }
    }
}

#[cfg(feature = "solver")]
#[test]
fn output_builder_consumers_refuse_capacity_and_separator_failures() {
    for (consumer, input, separators) in [
        (
            "png-dimensions",
            b"89504e470d0a1a0a0000000d494844520000032000000258".as_slice(),
            [120].as_slice(),
        ),
        (
            "word-frequency",
            b"red blue red".as_slice(),
            [44, 58].as_slice(),
        ),
    ] {
        for value in separators {
            let project = Project::consumer(consumer);
            repin_mutated_bytes_module(&project, "bytes_out", |text| {
                text.replace(
                "pub fn push_byte(out: Builder @Mut, value: i64) -> i64 {",
                &format!("pub fn push_byte(out: Builder @Mut, value: i64) -> i64 {{ if value == {value} {{out.error=-413;return -413;}} else {{}}"))
            });
            let package = compile_project(&project);
            assert!(
                matches!(
                    execute_probe(&package, input),
                    Err(sigil_runtime::ToolError::Trapped { .. })
                ),
                "{consumer} must refuse separator failure {value}, not publish a prefix"
            );
        }
        let project = Project::consumer(consumer);
        repin_mutated_bytes_module(&project, "bytes_out", |text| {
            text.replace(
                "return Builder { ptr: ptr, capacity: capacity, length: 0, error: 0 };",
                "return Builder { ptr: ptr, capacity: 0, length: 0, error: 0 };",
            )
        });
        let package = compile_project(&project);
        assert!(
            matches!(
                execute_probe(&package, input),
                Err(sigil_runtime::ToolError::Trapped { .. })
            ),
            "{consumer} must refuse insufficient output capacity"
        );
    }
}

#[cfg(feature = "solver")]
#[test]
fn fresh_starter_builder_upgrade_and_refresh_preserve_rollback() {
    let previous = Project::consumer_with_bytes(
        "png-dimensions",
        Some("library/packages/bytes/versions/0.1.0-public.3"),
    );
    let next = Project::consumer("png-dimensions");
    let old = previous.directory.join("reader-before");
    let candidate = previous.directory.join("reader-next");
    assert!(
        init_starter(&previous, &old, "builder-reader")
            .status
            .success()
    );
    assert!(
        init_starter(&next, &candidate, "builder-reader")
            .status
            .success()
    );
    let old_cert = previous.directory.join("before.cert.json");
    let old_path = old_cert.to_str().expect("cert path");
    assert!(
        starter_cli(&old, "check", &["--cert", old_path])
            .status
            .success()
    );
    let old_files = tree_bytes(&old);
    let old_cert_bytes = std::fs::read(&old_cert).expect("preserved rollback cert");
    let before_edit = previous.directory.join("before-edit.cert.json");
    let before_path = before_edit.to_str().expect("cert path");
    assert!(
        starter_cli(&candidate, "check", &["--cert", before_path])
            .status
            .success()
    );
    let before_bytes = std::fs::read(&before_edit).expect("pre-edit cert");
    std::fs::write(
        candidate.join("src/tool.sigil"),
        r#"module tool;
use sigil::bytes;
use sigil::bytes_out;
use sigil::fmt;
pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {Alloc} {
    let value=bytes::read_u32_le(input_ptr,input_len,0);
    if value<0 {return value;} else {}
    let out=bytes_out::new(10);
    bytes_out::append_output(out,fmt::decimal_i64(value));
    return bytes_out::finish(out);
}"#,
    )
    .expect("edit new candidate to use the builder");
    std::fs::write(candidate.join("API.md"),"# Private bounded header reader\n\nPublic four-byte little-endian input rendered via fmt and a fixed ten-byte builder; short input refuses. No host authority or admission.\n").expect("review edited API");
    assert!(
        !starter_cli(&candidate, "run", &["--input", "ABCD"])
            .status
            .success()
    );
    assert!(refresh_cli(&candidate, &[]).status.success());
    for path in [old_path, before_path] {
        assert!(
            !starter_cli(&candidate, "run", &["--input", "ABCD", "--cert", path])
                .status
                .success()
        );
    }
    let cert = previous.directory.join("next.cert.json");
    let path = cert.to_str().expect("cert path");
    assert!(
        starter_cli(&candidate, "check", &["--cert", path])
            .status
            .success()
    );
    for root in [&old, &candidate] {
        let selected = if root == &old { old_path } else { path };
        let result = starter_cli(root, "run", &["--input", "ABCD", "--cert", selected]);
        assert!(result.status.success());
        assert_eq!(envelope(&result)["data"]["output_text"], "1145258561");
        assert!(
            starter_cli(root, "verify-cert", &["--cert", selected])
                .status
                .success()
        );
    }
    assert!(
        !starter_cli(&candidate, "run", &["--input", "ABC"])
            .status
            .success()
    );
    assert!(
        !starter_cli(&candidate, "run", &["--input", "ABCD", "--fuel", "1"])
            .status
            .success()
    );
    let old_lock: serde_json::Value = serde_json::from_slice(
        &std::fs::read(old.join("sigil-package.lock.json")).expect("old graph"),
    )
    .expect("lock JSON");
    let next_lock: serde_json::Value = serde_json::from_slice(
        &std::fs::read(candidate.join("sigil-package.lock.json")).expect("new graph"),
    )
    .expect("lock JSON");
    let node = |value: &serde_json::Value, package: &str| {
        value["nodes"]
            .as_array()
            .expect("nodes")
            .iter()
            .find(|n| n["package"] == package)
            .expect("package")
            .clone()
    };
    assert_eq!(node(&old_lock, "sigil/bytes")["version"], "0.1.0-public.3");
    assert_eq!(node(&next_lock, "sigil/bytes")["version"], "0.1.0-public.4");
    assert_eq!(node(&old_lock, "sigil/fmt"), node(&next_lock, "sigil/fmt"));
    assert_eq!(
        tree_bytes(&old),
        old_files,
        "rollback root/lock/cache must remain byte-for-byte intact"
    );
    assert_eq!(
        std::fs::read(old_cert).expect("old cert preserved"),
        old_cert_bytes
    );
    assert_eq!(
        std::fs::read(before_edit).expect("stale cert preserved"),
        before_bytes
    );
}

#[cfg(feature = "solver")]
#[test]
fn bytes_fixed_vectors_preserve_memory_allocation_and_resource_bounds() {
    let vectors: serde_json::Value = serde_json::from_str(include_str!(
        "../../../library/contracts/bytes/fixtures/vectors.json"
    ))
    .expect("frozen byte-operation vectors");
    let mut cases: Vec<serde_json::Value> = vectors["vectors"]
        .as_array()
        .expect("vectors")
        .iter()
        .filter(|case| case["operation"] != "copy_into")
        .cloned()
        .collect();
    for (operation, len, offset, value, expected) in [
        ("read_u32_le", 4_i64, 0_i64, 0_i64, 4294967295_i64),
        ("read_u32_le", -1, 0, 0, -400),
        ("read_u32_le", 4, i64::MIN, 0, -400),
        ("read_u32_le", 4, i64::MAX, 0, -413),
        ("read_u32_le", 4, 4, 0, -413),
        ("write_u32_le", -1, 0, -1, -400),
        ("write_u32_le", 4, i64::MIN, -1, -400),
        ("write_u32_le", 4, i64::MAX, -1, -413),
        ("write_u32_le", 4, 1, -1, -413),
        ("write_u32_le", 4, 0, -1, -422),
        ("write_u32_le", 4, 0, i64::MIN, -422),
        ("write_u32_le", 4, 0, i64::MAX, -422),
    ] {
        cases.push(
            serde_json::json!({"operation":operation,"buffer_hex":"ffffffff",
            "len":len,"offset":offset,"value":value,"expected_result":expected}),
        );
    }
    for (value, bytes) in [
        (0_i64, "00000000"),
        (1, "01000000"),
        (255, "ff000000"),
        (256, "00010000"),
        (65535, "ffff0000"),
        (65536, "00000100"),
        (16777215, "ffffff00"),
        (16777216, "00000001"),
        (2147483648, "00000080"),
        (4294967294, "feffffff"),
    ] {
        let encoded = format!("aabb{bytes}cc");
        cases.push(
            serde_json::json!({"operation":"write_u32_le","buffer_hex":"aabbffffffffcc",
            "len":7,"offset":2,"value":value,"expected_result":6,"expected_hex":encoded}),
        );
        cases.push(
            serde_json::json!({"operation":"read_u32_le","buffer_hex":encoded,
            "len":7,"offset":2,"expected_result":value}),
        );
    }
    let checked_cases = cases.len() * 5;
    let mut max_read_fuel = 0;
    let mut max_write_fuel = 0;
    for (consumer, provider) in [
        ("edit-distance", Some("library/packages/bytes")),
        (
            "png-dimensions",
            Some("library/packages/bytes/versions/0.1.0-public.2"),
        ),
        (
            "png-dimensions",
            Some("library/packages/bytes/versions/0.1.0-public.3"),
        ),
        ("png-dimensions", None),
        ("word-frequency", None),
    ] {
        for case in &cases {
            let operation = case["operation"].as_str().expect("operation");
            let hex = case["buffer_hex"].as_str().expect("input hex");
            let decode = |hex: &str| {
                let (pairs, remainder) = hex.as_bytes().as_chunks::<2>();
                assert!(
                    remainder.is_empty(),
                    "fixed hex must contain complete bytes"
                );
                pairs
                    .iter()
                    .map(|pair| {
                        u8::from_str_radix(std::str::from_utf8(pair).expect("ASCII hex"), 16)
                            .expect("hex byte")
                    })
                    .collect::<Vec<_>>()
            };
            let input = decode(hex);
            let expected_memory = decode(case["expected_hex"].as_str().unwrap_or(hex));
            let expected_status = case["expected_result"].as_i64().expect("fixed result");
            // SIGIL parses unary minus after the unsigned literal. Spell MIN from
            // representable signed operands rather than accidentally requesting u256.
            let scalar = |field: &str| {
                if case[field].as_i64() == Some(i64::MIN) {
                    "(-9223372036854775807 - 1)".to_owned()
                } else {
                    case[field].to_string()
                }
            };
            let call = if operation == "read_u32_le" {
                format!(
                    "bytes::read_u32_le(input_ptr,{}, {})",
                    scalar("len"),
                    scalar("offset")
                )
            } else {
                format!(
                    "bytes::write_u32_le(input_ptr,{}, {}, {})",
                    scalar("len"),
                    scalar("offset"),
                    scalar("value")
                )
            };
            let project = Project::consumer_with_bytes(consumer, provider);
            let package = compile_bytes_probe(&project, &call, false);
            let certificate = package.certificate();
            let bytes = certificate
                .packages
                .iter()
                .find(|p| p.package == "sigil/bytes")
                .expect("bytes node");
            let scan_version = consumer == "word-frequency" && provider.is_none();
            let builder_version =
                (consumer == "png-dimensions" || scan_version) && provider.is_none();
            assert_eq!(
                bytes.modules,
                if scan_version {
                    vec!["bytes", "bytes_out", "bytes_scan"]
                } else if builder_version {
                    vec!["bytes", "bytes_out"]
                } else {
                    vec!["bytes"]
                }
            );
            assert_eq!(bytes.derived.rings, ["inner"]);
            let mut taint_contracts = vec![
                "bytes::read_u32_le(ptr:Public,len:Public,offset:Public)->Public".into(),
                "bytes::write_u32_le(ptr:Public,len:Public,offset:Public,value:Public)->Public"
                    .into(),
            ];
            if consumer == "png-dimensions" || scan_version {
                taint_contracts.insert(
                    0,
                    "bytes::read_u32_be(ptr:Public,len:Public,offset:Public)->Public".into(),
                );
                if provider != Some("library/packages/bytes/versions/0.1.0-public.2") {
                    taint_contracts.insert(0, "bytes::copy_into(dst_ptr:Public,dst_len:Public,dst_offset:Public,src_ptr:Public,src_len:Public,src_offset:Public,count:Public)->Public".into());
                }
            }
            if builder_version {
                taint_contracts.extend(output_taint_contracts());
            }
            if scan_version {
                taint_contracts.extend(scan_taint_contracts());
            }
            assert_eq!(
                bytes.derived,
                sigil_compiler::package::PackageDerivedFactsJson {
                    rings: vec!["inner".into()],
                    effects: if builder_version {
                        vec!["Alloc".into()]
                    } else {
                        vec![]
                    },
                    host_imports: vec![],
                    grant_categories: vec![],
                    trusted_surface: vec![],
                    package_imports: vec![],
                    ambient_imports: vec![],
                    taint_contracts,
                    taint_contract_hash: bytes.derived.taint_contract_hash.clone(),
                }
            );
            let observation = execute_probe(&package, &input).expect("bounded byte operation");
            let mut expected = format!("{expected_status}/0/").into_bytes();
            expected.extend(expected_memory);
            assert_eq!(observation.output, expected, "{case}");
            // Same driver/output lengths with a literal status isolate the operation's
            // fuel from formatting, buffer observation and allocation instrumentation.
            let baseline = Project::consumer_with_bytes(consumer, provider);
            let baseline = compile_bytes_probe(&baseline, &expected_status.to_string(), false);
            let control = execute_probe(&baseline, &input).expect("literal-status fuel control");
            let charged = observation
                .fuel_consumed
                .checked_sub(control.fuel_consumed)
                .expect("operation cannot refund driver fuel");
            assert!(
                charged <= if operation == "read_u32_le" { 128 } else { 160 },
                "{case}: {charged}"
            );
            if operation == "read_u32_le" {
                max_read_fuel = max_read_fuel.max(charged);
            } else {
                max_write_fuel = max_write_fuel.max(charged);
            }
        }
    }
    eprintln!(
        "bytes observations: {checked_cases} fixed cases; max read {max_read_fuel}, max write {max_write_fuel} SIGIL fuel above matched driver controls"
    );
    // SC-P4: allocation observation must detect a real positive allocation.
    let project = Project::consumer("edit-distance");
    let package = compile_bytes_probe(&project, "bytes::read_u32_le(input_ptr,4,0)", true);
    assert_eq!(
        execute_probe(&package, &[0; 4])
            .expect("planted allocation")
            .output,
        b"0/8/\0\0\0\0"
    );
}

#[cfg(feature = "solver")]
#[test]
fn bytes_mutations_are_detected_and_consumer_errors_are_not_distances() {
    let big_endian = Project::consumer("edit-distance");
    repin_mutated_bytes(&big_endian, |text| {
        text.replace(
            "b0 + b1 * 256 + b2 * 65536 + b3 * 16777216",
            "b3 + b2 * 256 + b1 * 65536 + b0 * 16777216",
        )
    });
    let package = compile_bytes_probe(&big_endian, "bytes::read_u32_le(input_ptr,4,0)", false);
    assert_ne!(
        execute_probe(&package, &[0x78, 0x56, 0x34, 0x12])
            .expect("big-endian mutation")
            .output,
        b"305419896/0/\x78\x56\x34\x12"
    );

    let partial_write = Project::consumer("edit-distance");
    repin_mutated_bytes(&partial_write, |text| {
        text.replace(
            "if value < 0 || value > 4294967295 {",
            "store8(ptr + offset, 0); if value < 0 || value > 4294967295 {",
        )
    });
    let package = compile_bytes_probe(
        &partial_write,
        "bytes::write_u32_le(input_ptr,4,0,-1)",
        false,
    );
    assert_ne!(
        execute_probe(&package, &[0xaa, 0xbb, 0xcc, 0xdd])
            .expect("partial-write mutation")
            .output,
        b"-422/0/\xaa\xbb\xcc\xdd"
    );

    let wrapping_bounds = Project::consumer("edit-distance");
    repin_mutated_bytes(&wrapping_bounds, |text| {
        text.replace("if offset > len {", "if offset + 4 > len {")
            .replace("if len - offset < 4 {", "if false {")
    });
    let package = compile_bytes_probe(
        &wrapping_bounds,
        "bytes::read_u32_le(input_ptr,4,9223372036854775805)",
        false,
    );
    match execute_probe(&package, &[0; 4]) {
        Ok(observation) => assert_ne!(
            observation.output, b"-413/0/\0\0\0\0",
            "wrapping must not satisfy the fixed bounds-error observation"
        ),
        Err(sigil_runtime::ToolError::Trapped { .. }) => {}
        Err(error) => panic!("unexpected mutation failure: {error:?}"),
    }

    let value_first = Project::consumer("edit-distance");
    repin_mutated_bytes(&value_first, |text| {
        text.replace(
            "value: i64) -> i64 {",
            "value: i64) -> i64 { if value < 0 || value > 4294967295 { return -422; } else {}",
        )
    });
    let package = compile_bytes_probe(
        &value_first,
        "bytes::write_u32_le(input_ptr,4,-1,4294967296)",
        false,
    );
    assert_ne!(
        execute_probe(&package, &[0; 4])
            .expect("precedence mutation")
            .output,
        b"-400/0/\0\0\0\0"
    );

    for (needle, replacement) in [
        (
            "return b0 + b1 * 256 + b2 * 65536 + b3 * 16777216;",
            "return -413;",
        ),
        ("return offset + 4;", "return -413;"),
    ] {
        let project = Project::consumer("edit-distance");
        repin_mutated_bytes(&project, |text| text.replace(needle, replacement));
        let package = compile_project(&project);
        for input in [b"kitten\nsitting".as_slice(), b"\n", b"abc"] {
            assert!(
                matches!(
                    execute_probe(&package, input),
                    Err(sigil_runtime::ToolError::Trapped { .. })
                ),
                "a byte-operation error must refuse, not become a distance"
            );
        }
    }
}

#[cfg(feature = "solver")]
#[test]
fn bytes_public_api_rejects_confidential_arguments_without_a_labeled_variant() {
    for call in [
        "bytes::read_u32_le(secret,4,0)",
        "bytes::read_u32_le(0,secret,0)",
        "bytes::read_u32_le(0,4,secret)",
        "bytes::write_u32_le(secret,4,0,0)",
        "bytes::write_u32_le(0,secret,0,0)",
        "bytes::write_u32_le(0,4,secret,0)",
        "bytes::write_u32_le(0,4,0,secret)",
    ] {
        for label in ["Public", "Internal", "Secret"] {
            let project = Project::consumer("edit-distance");
            let source = format!(
                "module tool; use sigil::bytes; use sigil::fmt; \
                fn sample(secret:i64 @{label})->i64 @{label} {{ return {call}; }} \
                pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{ return fmt::decimal_i64(0); }}"
            );
            std::fs::write(project.root.join("src/tool.sigil"), source).expect("write caller");
            project.lock();
            let output = project.cli("check", &[]);
            if label == "Public" {
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stdout)
                );
            } else {
                assert!(
                    !output.status.success(),
                    "confidential argument reached Public bytes API"
                );
                let value = envelope(&output);
                let codes: std::collections::BTreeSet<&str> = value["diagnostics"]
                    .as_array()
                    .expect("diagnostics")
                    .iter()
                    .map(|d| d["code"].as_str().expect("code"))
                    .collect();
                assert_eq!(
                    codes,
                    std::collections::BTreeSet::from([concat!("T", "001")])
                );
            }
        }
    }
}

#[cfg(feature = "solver")]
#[test]
fn copy_into_matches_fixed_and_overlapping_ranges_without_allocation() {
    let decode = |hex: &str| {
        let (pairs, remainder) = hex.as_bytes().as_chunks::<2>();
        assert!(
            remainder.is_empty(),
            "fixed hex must contain complete bytes"
        );
        pairs
            .iter()
            .map(|pair| {
                u8::from_str_radix(std::str::from_utf8(pair).expect("ASCII hex"), 16)
                    .expect("fixed byte")
            })
            .collect::<Vec<_>>()
    };
    let vectors: serde_json::Value = serde_json::from_str(include_str!(
        "../../../library/contracts/bytes/fixtures/vectors.json"
    ))
    .expect("frozen independent byte vectors");
    for case in vectors["vectors"]
        .as_array()
        .expect("vectors")
        .iter()
        .filter(|v| v["operation"] == "copy_into")
    {
        let project = Project::consumer("png-dimensions");
        let operation = format!(
            "bytes::copy_into(input_ptr,{}, {}, input_ptr,{}, {}, {})",
            case["dst_len"], case["dst_offset"], case["src_len"], case["src_offset"], case["count"]
        );
        let package = compile_bytes_probe(&project, &operation, false);
        let mut expected = format!("{}/0/", case["expected_result"]).into_bytes();
        expected.extend(decode(
            case["expected_hex"].as_str().expect("memory oracle"),
        ));
        assert_eq!(
            execute_probe(
                &package,
                &decode(case["buffer_hex"].as_str().expect("input"))
            )
            .expect("fixed copy")
            .output,
            expected,
            "{case}"
        );
    }
    // Rust's slice move is independent of the SIGIL branch/loop implementation.
    // Header and tail sentinels make out-of-destination writes observable too.
    let project = Project::consumer("png-dimensions");
    let package = compile_bytes_probe(
        &project,
        "bytes::copy_into(input_ptr+4,8,load8(input_ptr),input_ptr+4,8,load8(input_ptr+1),load8(input_ptr+2))",
        false,
    );
    let mut controls = std::collections::BTreeMap::new();
    for status in [-413, 0, 1, 2, 3, 4, 5, 6, 7, 8] {
        let baseline = Project::consumer("png-dimensions");
        controls.insert(
            status,
            compile_bytes_probe(&baseline, &status.to_string(), false),
        );
    }
    let mut observed = 0;
    let mut max_charged = 0;
    for dst in 0..=9_u8 {
        for src in 0..=9_u8 {
            for count in [0, 1, 2, 4, 7, 8, 9_u8] {
                let input = [
                    dst, src, count, 0xa5, b'a', b'b', b'c', b'd', b'e', b'f', b'g', b'h', 0x5a,
                ];
                let valid = dst <= 8 && src <= 8 && count <= 8 - dst && count <= 8 - src;
                let status = if valid { i64::from(dst + count) } else { -413 };
                let mut memory = input;
                if valid {
                    memory.copy_within(
                        4 + usize::from(src)..4 + usize::from(src + count),
                        4 + usize::from(dst),
                    );
                }
                let result = execute_probe(&package, &input).expect("bounded copy range");
                let mut expected = format!("{status}/0/").into_bytes();
                expected.extend(memory);
                assert_eq!(
                    result.output, expected,
                    "dst={dst}, src={src}, count={count}"
                );
                let control =
                    execute_probe(&controls[&status], &input).expect("matched status driver");
                let charged = result
                    .fuel_consumed
                    .checked_sub(control.fuel_consumed)
                    .expect("copy cannot refund fuel");
                let ceiling = if valid {
                    96 + 12 * u64::from(count)
                } else {
                    96
                };
                assert!(charged <= ceiling, "copy fuel {charged} exceeds {ceiling}");
                max_charged = max_charged.max(charged);
                observed += 1;
            }
        }
    }
    eprintln!(
        "copy observations: {observed} generated ranges; max {max_charged} SIGIL fuel above matched drivers"
    );
    for count in [16, 31, 32, 255, 256, 1024] {
        let input = (0..=count).map(|n| (n % 256) as u8).collect::<Vec<_>>();
        let mut moved = input.clone();
        moved.copy_within(0..count, 1);
        let project = Project::consumer("png-dimensions");
        let package = compile_bytes_probe(
            &project,
            &format!(
                "bytes::copy_into(input_ptr,{},1,input_ptr,{},0,{count})",
                count + 1,
                count + 1
            ),
            false,
        );
        let result = execute_probe(&package, &input).expect("larger overlapping copy");
        let mut expected = format!("{}/0/", count + 1).into_bytes();
        expected.extend(moved);
        assert_eq!(result.output, expected, "copy length {count}");
        let control = Project::consumer("png-dimensions");
        let baseline = compile_bytes_probe(&control, &(count + 1).to_string(), false);
        let baseline = execute_probe(&baseline, &input).expect("larger matched driver");
        let charged = result
            .fuel_consumed
            .checked_sub(baseline.fuel_consumed)
            .expect("matched copy control");
        assert!(
            charged <= 96 + 12 * count as u64,
            "copy length {count}: {charged}"
        );
        eprintln!(
            "large-copy observation: {count} bytes, {charged} SIGIL fuel above matched driver"
        );
    }
    for (call, status) in [
        ("bytes::copy_into(input_ptr,-1,0,input_ptr,4,0,1)", -400_i64),
        ("bytes::copy_into(input_ptr,4,-1,input_ptr,4,0,1)", -400),
        ("bytes::copy_into(input_ptr,4,0,input_ptr,-1,0,1)", -400),
        (
            "bytes::copy_into(input_ptr,4,0,input_ptr,4,(-9223372036854775807-1),1)",
            -400,
        ),
        ("bytes::copy_into(input_ptr,0,1,input_ptr,0,1,-1)", -400),
        (
            "bytes::copy_into(input_ptr,4,9223372036854775807,input_ptr,4,0,(-9223372036854775807-1))",
            -400,
        ),
        (
            "bytes::copy_into(input_ptr,(-9223372036854775807-1),9,input_ptr,4,0,1)",
            -400,
        ),
        (
            "bytes::copy_into(input_ptr,9223372036854775807,9223372036854775807,input_ptr,4,0,1)",
            -413,
        ),
        (
            "bytes::copy_into(input_ptr,4,0,input_ptr,9223372036854775807,9223372036854775807,1)",
            -413,
        ),
        (
            "bytes::copy_into(9223372036854775807,4,3,9223372036854775807,4,0,2)",
            -413,
        ),
        (
            "bytes::copy_into(9223372036854775807,9223372036854775807,9223372036854775807,(-9223372036854775807-1),0,0,0)",
            i64::MAX,
        ),
        (
            "bytes::copy_into(9223372036854775807,0,0,9223372036854775807,0,0,0)",
            0,
        ),
    ] {
        let project = Project::consumer("png-dimensions");
        let package = compile_bytes_probe(&project, call, false);
        assert_eq!(
            execute_probe(&package, b"abcd")
                .expect("validation before access")
                .output,
            format!("{status}/0/abcd").as_bytes()
        );
        let control = Project::consumer("png-dimensions");
        let baseline = compile_bytes_probe(&control, &status.to_string(), false);
        let control = execute_probe(&baseline, b"abcd").expect("error fuel control");
        let result = execute_probe(&package, b"abcd").expect("repeat stable result");
        assert!(
            result
                .fuel_consumed
                .checked_sub(control.fuel_consumed)
                .expect("matched driver")
                <= 96
        );
    }
    // SC-P4: prove that the zero-allocation observer detects live growth.
    let control = Project::consumer("png-dimensions");
    let package = compile_bytes_probe(
        &control,
        "bytes::copy_into(input_ptr,4,0,input_ptr,4,0,4)",
        true,
    );
    assert_eq!(
        execute_probe(&package, b"abcd")
            .expect("allocation positive control")
            .output,
        b"4/8/abcd"
    );
}

#[cfg(feature = "solver")]
#[test]
fn copy_into_mutations_and_confidential_arguments_are_rejected() {
    let mutant = Project::consumer("png-dimensions");
    repin_mutated_bytes(&mutant, |text| {
        text.replace("if dst > src && dst - src < count {", "if false {")
    });
    let package = compile_bytes_probe(
        &mutant,
        "bytes::copy_into(input_ptr,6,1,input_ptr,6,0,5)",
        false,
    );
    let result = execute_probe(&package, b"abcdef").expect("live forward-only mutation");
    assert_eq!(result.output, b"6/0/aaaaaa");
    assert_ne!(result.output, b"6/0/aabcde");
    let mutant = Project::consumer("png-dimensions");
    repin_mutated_bytes(&mutant, |text| {
        text.replace("store8(dst + i, load8(src + i));", "store8(dst + i, 0);")
    });
    let package = compile_bytes_probe(
        &mutant,
        "bytes::copy_into(input_ptr,4,0,input_ptr,4,0,4)",
        false,
    );
    assert_eq!(
        execute_probe(&package, b"abcd")
            .expect("live corrupt-copy mutation")
            .output,
        b"4/0/\0\0\0\0"
    );
    let mutant = Project::consumer("png-dimensions");
    repin_mutated_bytes(&mutant, |text| {
        text.replace(
        "    if dst_len < 0 || dst_offset < 0 || src_len < 0 || src_offset < 0 || count < 0 {",
        "    store8(dst_ptr, 0);\n    if dst_len < 0 || dst_offset < 0 || src_len < 0 || src_offset < 0 || count < 0 {",
    )
    });
    let package = compile_bytes_probe(
        &mutant,
        "bytes::copy_into(input_ptr,4,3,input_ptr,4,0,2)",
        false,
    );
    let result = execute_probe(&package, b"abcd").expect("live write-before-validation mutation");
    assert_eq!(result.output, b"-413/0/\0bcd");
    assert_ne!(
        result.output, b"-413/0/abcd",
        "error-memory observer must detect a premature write"
    );
    for argument in 0..7 {
        for label in ["Public", "Internal", "Secret"] {
            let project = Project::consumer("png-dimensions");
            let mut args = ["0"; 7];
            args[argument] = "value";
            let source = format!(
                "module tool; use sigil::bytes; use sigil::fmt; fn sample(value:i64 @{label})->i64 @{label} {{return bytes::copy_into({});}} pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return fmt::decimal_i64(0);}}",
                args.join(",")
            );
            std::fs::write(project.root.join("src/tool.sigil"), source)
                .expect("labeled copy caller");
            project.lock();
            let output = project.cli("check", &[]);
            if label == "Public" {
                assert!(output.status.success(), "Public accept twin");
            } else {
                assert!(!output.status.success());
                let value = envelope(&output);
                let codes = value["diagnostics"]
                    .as_array()
                    .expect("diagnostics")
                    .iter()
                    .map(|d| d["code"].as_str().expect("code"))
                    .collect::<std::collections::BTreeSet<_>>();
                assert_eq!(
                    codes,
                    std::collections::BTreeSet::from([concat!("T", "001")])
                );
            }
        }
    }
}

#[cfg(feature = "solver")]
#[test]
fn copy_consumers_refuse_errors_from_each_output_copy_site() {
    for (consumer, input) in [
        (
            "png-dimensions",
            b"89504e470d0a1a0a0000000d494844520000032000000258".as_slice(),
        ),
        ("word-frequency", b"red blue red".as_slice()),
    ] {
        for condition in ["dst_offset == 0", "dst_offset > 0"] {
            let project = Project::consumer(consumer);
            repin_mutated_bytes(&project, |text| {
                text.replace(
                    "    if count == 0 {",
                    &format!(
                        "    if {condition} {{ return -413; }} else {{}}\n    if count == 0 {{"
                    ),
                )
            });
            let package = compile_project(&project);
            assert!(
                matches!(
                    execute_probe(&package, input),
                    Err(sigil_runtime::ToolError::Trapped { .. })
                ),
                "{consumer} must propagate {condition} copy refusal"
            );
        }
    }
}

#[cfg(feature = "solver")]
#[test]
fn fresh_starter_copy_edit_runs_and_refuses_stale_certificates() {
    let project = Project::consumer("png-dimensions");
    let root = project.directory.join("copy-starter");
    assert!(
        init_starter(&project, &root, "copy-starter")
            .status
            .success()
    );
    let old_cert = project.directory.join("starter-before.cert.json");
    let old_path = old_cert.to_str().expect("cert path");
    assert!(
        starter_cli(&root, "check", &["--cert", old_path])
            .status
            .success()
    );
    let old_bytes = std::fs::read(&old_cert).expect("preserved initial cert");
    std::fs::write(
        root.join("src/tool.sigil"),
        include_str!("../../../library/programs/copy-reader/src/tool.sigil"),
    )
    .expect("edit to the documented program using shared copying");
    std::fs::write(
        root.join("API.md"),
        include_str!("../../../library/programs/copy-reader/API.md"),
    )
    .expect("review the edited application API");
    assert!(
        !starter_cli(&root, "run", &["--input", "ABCD"])
            .status
            .success()
    );
    assert!(refresh_cli(&root, &[]).status.success());
    assert!(
        !starter_cli(&root, "run", &["--input", "ABCD", "--cert", old_path])
            .status
            .success()
    );
    let cert = project.directory.join("starter-copy.cert.json");
    let path = cert.to_str().expect("fresh cert");
    assert!(
        starter_cli(&root, "check", &["--cert", path])
            .status
            .success()
    );
    let output = starter_cli(&root, "run", &["--input", "ABCD", "--cert", path]);
    assert!(output.status.success());
    assert_eq!(envelope(&output)["data"]["output_text"], "1145258561");
    assert!(
        starter_cli(&root, "verify-cert", &["--cert", path])
            .status
            .success()
    );
    assert!(
        !starter_cli(&root, "run", &["--input", "ABC"])
            .status
            .success()
    );
    assert!(
        !starter_cli(&root, "run", &["--input", "ABCD", "--fuel", "1"])
            .status
            .success()
    );
    assert_eq!(
        std::fs::read(old_cert).expect("old certificate unchanged"),
        old_bytes
    );
}

#[cfg(feature = "solver")]
#[test]
fn big_endian_reads_preserve_memory_and_meet_allocation_and_fuel_bounds() {
    let mut max_fuel = 0;
    let cases: &[(&[u8], &str, &str, i64)] = &[
        (&[0, 0, 0, 0], "4", "0", 0),
        (&[0, 0, 0, 1], "4", "0", 1),
        (&[0, 0, 1, 0], "4", "0", 256),
        (&[0, 1, 0, 0], "4", "0", 65536),
        (&[1, 0, 0, 0], "4", "0", 16777216),
        (&[1, 2, 3, 4], "4", "0", 16909060),
        (&[0x80, 0, 0, 0], "4", "0", 2147483648),
        (&[255, 255, 255, 255], "4", "0", 4294967295),
        (&[9, 1, 2, 3, 4, 8], "6", "1", 16909060),
        (&[1, 2, 3, 4], "-1", "0", -400),
        (&[1, 2, 3, 4], "4", "(-9223372036854775807 - 1)", -400),
        (&[1, 2, 3, 4], "(-9223372036854775807 - 1)", "0", -400),
        (&[1, 2, 3, 4], "4", "9223372036854775807", -413),
        (
            &[1, 2, 3, 4],
            "9223372036854775807",
            "9223372036854775804",
            -413,
        ),
        (&[1, 2, 3], "3", "0", -413),
        (&[1, 2, 3, 4], "4", "1", -413),
    ];
    for (input, len, offset, expected_status) in cases {
        let project = Project::consumer("png-dimensions");
        let call = format!("bytes::read_u32_be(input_ptr,{len},{offset})");
        let package = compile_bytes_probe(&project, &call, false);
        let observation = execute_probe(&package, input).expect("bounded big-endian read");
        let mut expected = format!("{expected_status}/0/").into_bytes();
        expected.extend_from_slice(input);
        assert_eq!(observation.output, expected, "len={len}, offset={offset}");
        let baseline = Project::consumer("png-dimensions");
        let baseline = compile_bytes_probe(&baseline, &expected_status.to_string(), false);
        let control = execute_probe(&baseline, input).expect("matched driver fuel control");
        let charged = observation
            .fuel_consumed
            .checked_sub(control.fuel_consumed)
            .expect("byte operation cannot refund driver fuel");
        assert!(charged <= 128, "read fuel ceiling: {charged}");
        max_fuel = max_fuel.max(charged);
        let certificate = package.certificate();
        let facts = &certificate
            .packages
            .iter()
            .find(|p| p.package == "sigil/bytes")
            .expect("bytes package")
            .derived;
        assert_eq!(facts.rings, ["inner"]);
        assert_eq!(facts.effects, ["Alloc"]);
        assert_eq!(facts.host_imports, Vec::<String>::new());
        assert_eq!(facts.grant_categories, Vec::<String>::new());
        assert_eq!(facts.trusted_surface, Vec::<String>::new());
        let mut contracts: Vec<String> = [
                "bytes::copy_into(dst_ptr:Public,dst_len:Public,dst_offset:Public,src_ptr:Public,src_len:Public,src_offset:Public,count:Public)->Public",
                "bytes::read_u32_be(ptr:Public,len:Public,offset:Public)->Public",
                "bytes::read_u32_le(ptr:Public,len:Public,offset:Public)->Public",
                "bytes::write_u32_le(ptr:Public,len:Public,offset:Public,value:Public)->Public",
            ].into_iter().map(str::to_owned).collect();
        contracts.extend(output_taint_contracts());
        assert_eq!(facts.taint_contracts, contracts);
    }
    eprintln!(
        "big-endian observations: {} fixed cases; max {max_fuel} SIGIL fuel above matched driver controls",
        cases.len()
    );
    // SC-P4: the zero-growth detector must observe a real positive allocation.
    let allocation = Project::consumer("png-dimensions");
    let package = compile_bytes_probe(&allocation, "bytes::read_u32_be(input_ptr,4,0)", true);
    assert_eq!(
        execute_probe(&package, &[1, 2, 3, 4])
            .expect("allocation control")
            .output,
        b"16909060/8/\x01\x02\x03\x04"
    );
    let early = Project::consumer("png-dimensions");
    let package = compile_bytes_probe(
        &early,
        "bytes::read_u32_be(9223372036854775807,-1,0)",
        false,
    );
    assert_eq!(
        execute_probe(&package, &[1, 2, 3, 4])
            .expect("scalar rejection precedes load")
            .output,
        b"-400/0/\x01\x02\x03\x04"
    );
}

#[cfg(feature = "solver")]
#[test]
fn big_endian_mutations_and_confidential_arguments_are_rejected() {
    let mutant = Project::consumer("png-dimensions");
    repin_mutated_bytes(&mutant, |text| {
        text.replace(
            "return b0 * 16777216 + b1 * 65536 + b2 * 256 + b3;",
            "return b0 + b1 * 256 + b2 * 65536 + b3 * 16777216;",
        )
    });
    let package = compile_bytes_probe(&mutant, "bytes::read_u32_be(input_ptr,4,0)", false);
    assert_eq!(
        execute_probe(&package, &[1, 2, 3, 4])
            .expect("live wrong-endian mutant")
            .output,
        b"67305985/0/\x01\x02\x03\x04"
    );
    assert_ne!(
        execute_probe(&package, &[1, 2, 3, 4])
            .expect("fixed-answer comparator")
            .output,
        b"16909060/0/\x01\x02\x03\x04"
    );
    for call in [
        "bytes::read_u32_be(secret,4,0)",
        "bytes::read_u32_be(0,secret,0)",
        "bytes::read_u32_be(0,4,secret)",
    ] {
        for label in ["Public", "Internal", "Secret"] {
            let project = Project::consumer("png-dimensions");
            std::fs::write(project.root.join("src/tool.sigil"), format!(
                "module tool; use sigil::bytes; use sigil::fmt; \
                 fn sample(secret:i64 @{label})->i64 @{label} {{ return {call}; }} \
                 pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{ return fmt::decimal_i64(0); }}"
            )).expect("write labeled caller");
            project.lock();
            let output = project.cli("check", &[]);
            if label == "Public" {
                assert!(output.status.success(), "Public twin must compile");
            } else {
                assert!(!output.status.success());
                let value = envelope(&output);
                let codes = value["diagnostics"]
                    .as_array()
                    .expect("diagnostics")
                    .iter()
                    .map(|d| d["code"].as_str().expect("code"))
                    .collect::<std::collections::BTreeSet<_>>();
                assert_eq!(
                    codes,
                    std::collections::BTreeSet::from([concat!("T", "001")])
                );
            }
        }
    }
}

#[test]
fn changing_selected_dependency_is_rejected_without_repinning_or_publication() {
    let project = Project::new();
    let source = project.dependency.join("src/fmt.sigil");
    let mut text = std::fs::read_to_string(&source).expect("read dependency");
    text.push_str("\n// different content\n");
    std::fs::write(source, text).expect("mutate selected dependency");
    let error = create_local_package_lock_with_dependencies(&project.root, &project.selections())
        .expect_err("stale pin refused");
    assert_eq!(error.code, "E_HASH_MISMATCH");
    assert!(!project.root.join("sigil-package.lock.json").exists());
    assert!(!project.root.join(".sigil").exists());
}

#[test]
fn missing_extra_duplicate_and_wrong_identity_sources_fail_closed() {
    let project = Project::new();
    // The root manifest names `sigil/fmt`; with no source selected for it the
    // dependency walk finds no locked node. Exact code, not `is_err()`: any
    // earlier refusal (a manifest or limit error) would otherwise pass as this.
    assert_eq!(
        create_local_package_lock_with_dependencies(&project.root, &[])
            .expect_err("unselected dependency")
            .code,
        "E_OFFLINE_MISS"
    );
    let mut selections = project.selections();
    selections[0].package = "sigil/other".to_owned();
    assert_eq!(
        create_local_package_lock_with_dependencies(&project.root, &selections)
            .expect_err("wrong identity")
            .code,
        "E_SOURCE_CONFLICT"
    );
    let mut selections = project.selections();
    selections.push(selections[0].clone());
    assert_eq!(
        create_local_package_lock_with_dependencies(&project.root, &selections)
            .expect_err("duplicate identity")
            .code,
        "E_SOURCE_CONFLICT"
    );
    project.edit_manifest(|value| value["dependencies"] = serde_json::json!([]));
    assert_eq!(
        create_local_package_lock_with_dependencies(&project.root, &project.selections())
            .expect_err("unreachable explicit source")
            .code,
        "E_LOCK_DRIFT"
    );
}

#[test]
fn feature_selection_is_refused_and_cache_symlinks_are_not_followed() {
    let project = Project::new();
    project.edit_manifest(|value| value["dependencies"][0]["optional"] = true.into());
    assert_eq!(
        create_local_package_lock_with_dependencies(&project.root, &project.selections())
            .expect_err("optional dependency")
            .code,
        "E_MANIFEST"
    );
    let project = Project::new();
    std::os::unix::fs::symlink(&project.directory, project.root.join(".sigil"))
        .expect("make cache symlink");
    assert_eq!(
        create_local_package_lock_with_dependencies(&project.root, &project.selections())
            .expect_err("symlink cache")
            .code,
        "E_MANIFEST"
    );
    assert!(!project.directory.join("deps").exists());
}

#[test]
fn cached_source_mutation_and_root_mutation_are_detected_by_the_loader() {
    let project = Project::new();
    let bytes = project.lock();
    std::fs::write(cached_source(&project, &bytes), "module fmt;\n").expect("mutate cache");
    assert_eq!(
        load_graph(&project.root).expect_err("cache drift").code,
        "E_HASH_MISMATCH"
    );
    let project = Project::new();
    project.lock();
    std::fs::write(project.root.join("src/tool.sigil"), "module tool;\n").expect("mutate root");
    assert_eq!(
        load_graph(&project.root).expect_err("source drift").code,
        "E_HASH_MISMATCH"
    );
}

#[test]
fn package_only_flags_and_fuel_limits_are_enforced() {
    let project = Project::new();
    for (verb, flags) in [
        ("check", vec!["--input", "a"]),
        ("run", vec!["--fuel", "0"]),
        ("run", vec!["--fuel", "10000001"]),
        ("run", vec!["--serve"]),
    ] {
        let output = project.cli(verb, &flags);
        assert!(!output.status.success());
        assert_eq!(
            envelope(&output)["diagnostics"][0]["code"],
            concat!("R", "800")
        );
    }
}

#[cfg(not(feature = "solver"))]
#[test]
fn solver_off_package_run_refuses_even_with_legacy_override() {
    for name in [
        "split-count",
        "bracket-match",
        "edit-distance",
        "word-frequency",
        "png-dimensions",
    ] {
        let project = Project::consumer(name);
        project.lock();
        for verb in ["check", "run"] {
            let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
                .args([verb, "--package"])
                .arg(&project.root)
                .arg("--json")
                .env("SIGIL_ALLOW_UNVERIFIED_CERT", "1")
                .output()
                .expect("invoke solver-off CLI");
            assert!(!output.status.success());
            assert_eq!(
                envelope(&output)["diagnostics"][0]["code"],
                concat!("R", "817")
            );
        }
    }
}

#[cfg(feature = "solver")]
#[test]
fn png_dimensions_match_fixed_headers_and_reject_malformed_inputs() {
    let project = Project::consumer("png-dimensions");
    let package = compile_project(&project);
    let header = |width: u32, height: u32| {
        format!("89504e470d0a1a0a0000000d49484452{width:08x}{height:08x}")
    };
    for (width, height, expected) in [
        (1, 1, "1x1"),
        (9, 10, "9x10"),
        (800, 600, "800x600"),
        (255, 256, "255x256"),
        (65535, 65536, "65535x65536"),
        (16909060, 67305985, "16909060x67305985"),
        (2147483647, 2147483647, "2147483647x2147483647"),
    ] {
        let input = header(width, height);
        for text in [input.clone(), input.to_uppercase()] {
            assert_eq!(
                execute_probe(&package, text.as_bytes())
                    .expect("fixed header executes")
                    .output,
                expected.as_bytes()
            );
        }
    }
    let valid = header(800, 600);
    let mut invalid = Vec::new();
    for length in 0..48 {
        invalid.push(valid.as_bytes()[..length].to_vec());
    }
    for suffix in ["0", "00", "\n", " ", "abcdef"] {
        invalid.push(format!("{valid}{suffix}").into_bytes());
    }
    invalid.push(format!("0x{valid}").into_bytes());
    for offset in 0..48 {
        for bad in [b'g', b'/', b':', b'@', b'`', b' ', 0, 255] {
            let mut bytes = valid.as_bytes().to_vec();
            bytes[offset] = bad;
            invalid.push(bytes);
        }
    }
    // Corrupt each signature/type byte and vary the declared IHDR size.
    for offset in (0..16).chain(24..32) {
        let mut bytes = valid.as_bytes().to_vec();
        bytes[offset] = if bytes[offset] == b'0' { b'1' } else { b'0' };
        invalid.push(bytes);
    }
    for length in [0, 12, 14, 2147483647u32] {
        invalid.push(format!("89504e470d0a1a0a{length:08x}494844520000032000000258").into_bytes());
    }
    for (width, height) in [
        (0, 600),
        (800, 0),
        (0, 0),
        (2147483648, 600),
        (800, 2147483648),
        (u32::MAX, 600),
        (800, u32::MAX),
    ] {
        invalid.push(header(width, height).into_bytes());
    }
    for input in invalid {
        assert!(
            matches!(
                execute_probe(&package, &input),
                Err(sigil_runtime::ToolError::Trapped { .. })
            ),
            "invalid input must refuse without fabricated dimensions: {input:?}"
        );
    }
    // SC-P4: execute a wrong-width mutant to prove the fixed-answer comparison detects it.
    let mutant = Project::consumer("png-dimensions");
    let path = mutant.root.join("src/tool.sigil");
    let source = std::fs::read_to_string(&path).expect("mutation source");
    std::fs::write(
        &path,
        source.replace("fmt::decimal_i64(width)", "fmt::decimal_i64(width + 1)"),
    )
    .expect("plant wrong width");
    let mutant = compile_project(&mutant);
    assert_eq!(
        execute_probe(&mutant, valid.as_bytes())
            .expect("live mutant")
            .output,
        b"801x600"
    );
    let mutant = Project::consumer("png-dimensions");
    let path = mutant.root.join("src/tool.sigil");
    let source = std::fs::read_to_string(&path).expect("range mutation source");
    std::fs::write(
        &path,
        source.replace("if width == 0 { return -422; } else {}", ""),
    )
    .expect("plant missing zero-width guard");
    let mutant = compile_project(&mutant);
    assert_eq!(
        execute_probe(&mutant, header(0, 600).as_bytes())
            .expect("missing guard executes")
            .output,
        b"0x600"
    );
    let mutant = Project::consumer("png-dimensions");
    repin_mutated_bytes(&mutant, |text| {
        text.replace(
            "return b0 * 16777216 + b1 * 65536 + b2 * 256 + b3;",
            "return -413;",
        )
    });
    let mutant = compile_project(&mutant);
    assert!(matches!(
        execute_probe(&mutant, valid.as_bytes()),
        Err(sigil_runtime::ToolError::Trapped { .. })
    ));
}

#[cfg(feature = "solver")]
#[test]
fn png_cli_uses_hex_input_and_preserves_certificate_and_budget_refusals() {
    let project = Project::consumer("png-dimensions");
    let locked = project.lock();
    let cert = project.directory.join("png.cert.json");
    let cert_path = cert.to_str().expect("temporary cert path");
    let output = project.cli("check", &["--cert", cert_path]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let certificate = std::fs::read(&cert).expect("fresh graph certificate");
    let complete_png =
        include_str!("../../../library/programs/png-dimensions/fixtures/one-pixel.png.hex");
    for (input, expected) in [
        (&complete_png[..48], "1x1"),
        (
            "89504e470d0a1a0a0000000d494844520000032000000258",
            "800x600",
        ),
        (
            "89504E470D0A1A0A0000000D494844527FFFFFFF7FFFFFFF",
            "2147483647x2147483647",
        ),
    ] {
        let output = project.cli("run", &["--input", input, "--cert", cert_path]);
        assert!(output.status.success());
        assert_eq!(envelope(&output)["data"]["output_text"], expected);
        assert_eq!(envelope(&output)["data"]["admission"], "not_evaluated");
        let raw = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["run", "--package"])
            .arg(&project.root)
            .args(["--input", input])
            .output()
            .expect("raw PNG output");
        assert!(raw.status.success());
        assert_eq!(raw.stdout, expected.as_bytes());
    }
    for input in [
        "",
        "89504e47",
        "89504e470d0a1a0a0000000d494844520000000000000258",
    ] {
        let output = project.cli("run", &["--input", input]);
        assert!(!output.status.success());
        assert_eq!(
            envelope(&output)["diagnostics"][0]["code"],
            concat!("R", "803")
        );
    }
    let output = project.cli(
        "run",
        &[
            "--input",
            "89504e470d0a1a0a0000000d494844520000032000000258",
            "--fuel",
            "1",
        ],
    );
    assert!(!output.status.success());
    assert_eq!(
        envelope(&output)["diagnostics"][0]["code"],
        concat!("R", "801")
    );
    assert!(
        project
            .cli("verify-cert", &["--cert", cert_path])
            .status
            .success()
    );
    assert_eq!(std::fs::read(&cert).expect("preserved cert"), certificate);
    assert_eq!(
        std::fs::read(project.root.join("sigil-package.lock.json")).expect("preserved lock"),
        locked
    );
}

#[cfg(feature = "solver")]
#[test]
fn word_frequency_migration_preserves_byte_counts_order_and_error_refusal() {
    let project = Project::consumer("word-frequency");
    let package = compile_project(&project);
    let before = sigil_compiler::compile_named_module(
        "word_frequency_before.sigil",
        include_str!("../../../tools/task096_word_frequency.sigil"),
    )
    .expect("compile unchanged word-frequency reference");
    let mut cases: Vec<(Vec<u8>, Vec<u8>)> = vec![
        (b"".to_vec(), b"".to_vec()),
        (b" \t\r\n \t".to_vec(), b"".to_vec()),
        (b"red blue red".to_vec(), b"red:2,blue:1".to_vec()),
        (b"b a b c a".to_vec(), b"b:2,a:2,c:1".to_vec()),
        (b" a a ".to_vec(), b"a:2".to_vec()),
        (
            b"Word word WORD Word".to_vec(),
            b"Word:2,word:1,WORD:1".to_vec(),
        ),
        (
            b"alpha\tbeta\nalpha\rbeta".to_vec(),
            b"alpha:2,beta:2".to_vec(),
        ),
        (b", : ,".to_vec(), b",:2,::1".to_vec()),
        (b"a,b a,b a:b".to_vec(), b"a,b:2,a:b:1".to_vec()),
        (
            b"\x0b\x0c\x0b \x0b\x0c\x0b".to_vec(),
            b"\x0b\x0c\x0b:2".to_vec(),
        ),
        (b"\0 \0 \x01".to_vec(), b"\0:2,\x01:1".to_vec()),
        (b"\xff \x80 \xff".to_vec(), b"\xff:2,\x80:1".to_vec()),
        ("é e é".as_bytes().to_vec(), "é:2,e:1".as_bytes().to_vec()),
        (b"a\x0bb a\x0bb".to_vec(), b"a\x0bb:2".to_vec()),
    ];
    // Fixed answers cross decimal-count carries and the u32 metadata offsets.
    for (size, answer) in [
        (9, "a:9"),
        (10, "a:10"),
        (99, "a:99"),
        (100, "a:100"),
        (255, "a:255"),
        (256, "a:256"),
    ] {
        cases.push((b"a ".repeat(size), answer.as_bytes().to_vec()));
    }
    let mut long = vec![b'a'; 300];
    long.extend_from_slice(b" b ");
    long.extend(vec![b'a'; 300]);
    let mut answer = vec![b'a'; 300];
    answer.extend_from_slice(b":2,b:1");
    cases.push((long, answer));
    for (input, expected) in &cases {
        for wasm in [&before.wasm_inner, &package.compilation.wasm_inner] {
            let output = sigil_runtime::execute_ephemeral_with_budgets(
                wasm,
                input,
                100_000,
                10_000_000,
                16 * 1024 * 1024,
                &sigil_runtime::IoGrants::none(),
            )
            .expect("bounded word-frequency case");
            assert_eq!(&output.output, expected, "input={input:?}");
        }
    }
    // SC-P4: a live offset-count mutation must disagree with the fixed answers.
    let mutant = Project::consumer("word-frequency");
    let source = mutant.root.join("src/tool.sigil");
    let text = std::fs::read_to_string(&source).expect("read mutation input");
    let changed = text.replace("fmt::decimal_i64(count)", "fmt::decimal_i64(count + 1)");
    assert_ne!(
        changed, text,
        "the count mutation must change the migrated call site"
    );
    std::fs::write(source, changed).expect("plant count-offset mutation");
    let mutant = compile_project(&mutant);
    assert_ne!(
        execute_probe(&mutant, b"red blue red")
            .expect("execute count mutant")
            .output,
        b"red:2,blue:1"
    );
    for (needle, replacement) in [
        (
            "return b0 + b1 * 256 + b2 * 65536 + b3 * 16777216;",
            "return -413;",
        ),
        ("return offset + 4;", "return -413;"),
    ] {
        let project = Project::consumer("word-frequency");
        repin_mutated_bytes(&project, |text| text.replace(needle, replacement));
        let package = compile_project(&project);
        for input in [b"red blue red".as_slice(), b"a", b" a "] {
            assert!(
                matches!(
                    execute_probe(&package, input),
                    Err(sigil_runtime::ToolError::Trapped { .. })
                ),
                "byte errors must refuse before they become metadata or counts"
            );
        }
    }
}

#[cfg(feature = "solver")]
#[test]
fn word_frequency_cli_runs_the_composed_graph_and_enforces_fuel() {
    let project = Project::consumer("word-frequency");
    let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["package-lock", "--root"])
        .arg(&project.root)
        .arg("--dependency")
        .arg(format!("sigil/fmt={}", project.dependency.display()))
        .arg("--dependency")
        .arg(format!(
            "sigil/bytes={}",
            project
                .bytes_dependency
                .as_ref()
                .expect("bytes source")
                .display()
        ))
        .arg("--json")
        .output()
        .expect("lock word-frequency through CLI");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let cert = project.directory.join("word-frequency.cert.json");
    let output = project.cli("check", &["--cert", cert.to_str().expect("temp path")]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let certificate = std::fs::read(&cert).expect("read fresh certificate");
    for (input, expected) in [
        ("red blue red", "red:2,blue:1"),
        ("b a b c a", "b:2,a:2,c:1"),
        (" \t\r\n", ""),
    ] {
        let output = project.cli(
            "run",
            &[
                "--input",
                input,
                "--cert",
                cert.to_str().expect("temp path"),
            ],
        );
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert_eq!(envelope(&output)["data"]["output_text"], expected);
        let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["run", "--package"])
            .arg(&project.root)
            .args(["--input", input])
            .output()
            .expect("run raw-output word-frequency CLI");
        assert!(output.status.success());
        assert_eq!(output.stdout, expected.as_bytes());
    }
    assert_eq!(
        std::fs::read(&cert).expect("supplied certificate preserved"),
        certificate
    );
    let output = project.cli("run", &["--input", "red blue red", "--fuel", "1"]);
    assert!(!output.status.success());
    assert_eq!(
        envelope(&output)["diagnostics"][0]["code"],
        concat!("R", "801")
    );
}

#[cfg(feature = "solver")]
#[test]
fn bracket_migration_matches_fixed_byte_cases_and_kills_inverted_results() {
    let project = Project::consumer("bracket-match");
    project.lock();
    let compile = |root: &std::path::Path| {
        sigil_compiler::package::compile_local_package_with_context(
            root,
            sigil_compiler::CompileOptions::default(),
            &sigil_compiler::CompilerContext::default(),
        )
        .expect("solver compile bracket graph")
    };
    let package = compile(&project.root);
    let before = sigil_compiler::compile_named_module(
        "bracket_match_before.sigil",
        include_str!("../../../tools/task092_validate_bracket_matching.sigil"),
    )
    .expect("compile unchanged bracket reference");
    let execute = |wasm: &[u8], input: &[u8]| {
        sigil_runtime::execute_ephemeral_with_budgets(
            wasm,
            input,
            100_000,
            10_000_000,
            16 * 1024 * 1024,
            &sigil_runtime::IoGrants::default(),
        )
        .expect("bounded bracket execution")
        .output
    };
    let mut cases: Vec<(Vec<u8>, bool)> = vec![
        (b"".to_vec(), true),
        (b"plain text".to_vec(), true),
        (b"()".to_vec(), true),
        (b"[]".to_vec(), true),
        (b"{}".to_vec(), true),
        (b"()[]{}".to_vec(), true),
        (b"a{b[c(d)e]f}g".to_vec(), true),
        (b"([)]".to_vec(), false),
        (b"(]".to_vec(), false),
        (b"[}".to_vec(), false),
        (b"{)".to_vec(), false),
        (b"(".to_vec(), false),
        (b"[".to_vec(), false),
        (b"{".to_vec(), false),
        (b")".to_vec(), false),
        (b"]".to_vec(), false),
        (b"}".to_vec(), false),
        (b"())(".to_vec(), false),
        (b"x)()".to_vec(), false),
        (b"\"(\"".to_vec(), false),
        (b"// ]".to_vec(), false),
        ("α{β[γ(δ)ε]ζ}η".as_bytes().to_vec(), true),
        (vec![255, 40, 0, 128, 41], true),
        (vec![255, 40, 0, 93, 128], false),
    ];
    for pair in [(40, 41), (91, 93), (123, 125)] {
        let mut input = vec![pair.0; 256];
        input.extend(vec![pair.1; 256]);
        cases.push((input.clone(), true));
        input.push(pair.1);
        cases.push((input, false));
    }
    for (input, valid) in &cases {
        let expected: &[u8] = if *valid { b"true" } else { b"false" };
        for wasm in [&before.wasm_inner, &package.compilation.wasm_inner] {
            assert_eq!(execute(wasm, input), expected, "input={input:?}");
        }
    }
    // SC-P4: prove the before/after comparison detects a live semantic mutation.
    // Recompile an inverted formatter call rather than inspecting source text.
    let mutant = Project::consumer("bracket-match");
    let source = mutant.root.join("src/tool.sigil");
    let text = std::fs::read_to_string(&source).expect("read mutation input");
    std::fs::write(source, text.replace("valid == 1);", "valid != 1);"))
        .expect("plant inverted output mutation");
    mutant.lock();
    let mutant = compile(&mutant.root);
    for (input, valid) in [(b"()".as_slice(), true), (b"([)]".as_slice(), false)] {
        let expected: &[u8] = if valid { b"true" } else { b"false" };
        assert_eq!(execute(&package.compilation.wasm_inner, input), expected);
        assert_ne!(execute(&mutant.compilation.wasm_inner, input), expected);
    }
}

#[cfg(feature = "solver")]
#[test]
fn bracket_cli_runs_both_results_and_enforces_fuel() {
    let project = Project::consumer("bracket-match");
    let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["package-lock", "--root"])
        .arg(&project.root)
        .arg("--dependency")
        .arg(format!("sigil/fmt={}", project.dependency.display()))
        .arg("--json")
        .output()
        .expect("lock bracket package through CLI");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let cert = project.directory.join("bracket.cert.json");
    let output = project.cli("check", &["--cert", cert.to_str().expect("temp path")]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let certificate = std::fs::read(&cert).expect("read fresh bracket certificate");
    for (input, expected) in [("a{b[c(d)e]f}g", "true"), ("([)]", "false"), ("", "true")] {
        let output = project.cli(
            "run",
            &[
                "--input",
                input,
                "--cert",
                cert.to_str().expect("temp path"),
            ],
        );
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert_eq!(envelope(&output)["data"]["output_text"], expected);
        let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["run", "--package"])
            .arg(&project.root)
            .args(["--input", input])
            .output()
            .expect("run human-output bracket CLI");
        assert!(output.status.success());
        assert_eq!(output.stdout, expected.as_bytes());
    }
    assert_eq!(
        std::fs::read(&cert).expect("read supplied certificate"),
        certificate
    );
    let output = project.cli("run", &["--input", "()", "--fuel", "1"]);
    assert!(!output.status.success());
    assert_eq!(
        envelope(&output)["diagnostics"][0]["code"],
        concat!("R", "801")
    );
}

#[cfg(feature = "solver")]
#[test]
fn edit_distance_migration_matches_fixed_byte_cases_and_kills_offset_results() {
    let project = Project::consumer("edit-distance");
    project.lock();
    let compile = |root: &std::path::Path| {
        sigil_compiler::package::compile_local_package_with_context(
            root,
            sigil_compiler::CompileOptions::default(),
            &sigil_compiler::CompilerContext::default(),
        )
        .expect("solver compile edit-distance graph")
    };
    let package = compile(&project.root);
    let before = sigil_compiler::compile_named_module(
        "edit_distance_before.sigil",
        include_str!("../../../tools/task098_levenshtein_distance.sigil"),
    )
    .expect("compile unchanged edit-distance reference");
    let execute = |wasm: &[u8], input: &[u8]| {
        sigil_runtime::execute_ephemeral_with_budgets(
            wasm,
            input,
            100_000,
            10_000_000,
            16 * 1024 * 1024,
            &sigil_runtime::IoGrants::default(),
        )
        .expect("bounded edit-distance execution")
        .output
    };
    let mut cases: Vec<(Vec<u8>, &str)> = vec![
        (b"".to_vec(), "0"),
        (b"\n".to_vec(), "0"),
        (b"abc".to_vec(), "3"),
        (b"\nabc".to_vec(), "3"),
        (b"abc\n".to_vec(), "3"),
        (b"a\na".to_vec(), "0"),
        (b"a\nb".to_vec(), "1"),
        (b"ab\nba".to_vec(), "2"),
        (b"kitten\nsitting".to_vec(), "3"),
        (b"sitting\nkitten".to_vec(), "3"),
        (b"saturday\nsunday".to_vec(), "3"),
        (b"flaw\nlawn".to_vec(), "2"),
        (b"book\nback".to_vec(), "2"),
        (b"abc\nxyz".to_vec(), "3"),
        (b"same\nsame".to_vec(), "0"),
        (b"a\nb\nc".to_vec(), "3"),
        (b"\n\n".to_vec(), "1"),
        (b"a\r\nb\r".to_vec(), "1"),
        ("é\ne".as_bytes().to_vec(), "2"),
        ("α\nβ".as_bytes().to_vec(), "1"),
        (vec![255, 0, 10, 255, 128], "1"),
        (vec![128, 10, 255], "1"),
        (b"a\0b\na\0c".to_vec(), "1"),
        (b"ca\nac".to_vec(), "2"),
    ];
    // Fixed empty-side answers cross both decimal and four-byte row-cell carries.
    for (size, expected) in [
        (9, "9"),
        (10, "10"),
        (99, "99"),
        (100, "100"),
        (255, "255"),
        (256, "256"),
    ] {
        let mut left_only = vec![b'a'; size];
        left_only.push(10);
        cases.push((left_only, expected));
        let mut right_only = vec![10];
        right_only.extend(vec![b'b'; size]);
        cases.push((right_only, expected));
    }
    let mut square = vec![b'a'; 32];
    square.push(10);
    square.extend(vec![b'a'; 32]);
    cases.push((square, "0"));
    let mut square = vec![b'a'; 32];
    square.push(10);
    square.extend(vec![b'b'; 32]);
    cases.push((square, "32"));
    for (input, expected) in &cases {
        for wasm in [&before.wasm_inner, &package.compilation.wasm_inner] {
            assert_eq!(execute(wasm, input), expected.as_bytes(), "input={input:?}");
        }
    }
    // SC-P4: the comparator must detect a live wrong-distance result, not merely
    // agree because both paths failed to execute. Compile an offset mutation.
    let mutant = Project::consumer("edit-distance");
    let source = mutant.root.join("src/tool.sigil");
    let text = std::fs::read_to_string(&source).expect("read mutation input");
    std::fs::write(
        source,
        text.replace("fmt::decimal_i64(result);", "fmt::decimal_i64(result + 1);"),
    )
    .expect("plant offset-result mutation");
    mutant.lock();
    let mutant = compile(&mutant.root);
    for (input, expected) in [
        (b"a\na".as_slice(), "0"),
        (b"kitten\nsitting".as_slice(), "3"),
    ] {
        assert_eq!(
            execute(&package.compilation.wasm_inner, input),
            expected.as_bytes()
        );
        assert_ne!(
            execute(&mutant.compilation.wasm_inner, input),
            expected.as_bytes()
        );
    }
}

#[cfg(feature = "solver")]
#[test]
fn edit_distance_cli_runs_two_line_inputs_and_enforces_fuel() {
    let project = Project::consumer("edit-distance");
    let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["package-lock", "--root"])
        .arg(&project.root)
        .arg("--dependency")
        .arg(format!("sigil/fmt={}", project.dependency.display()))
        .arg("--dependency")
        .arg(format!(
            "sigil/bytes={}",
            project
                .bytes_dependency
                .as_ref()
                .expect("bytes source")
                .display()
        ))
        .arg("--json")
        .output()
        .expect("lock edit-distance package through CLI");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let cert = project.directory.join("edit-distance.cert.json");
    let output = project.cli("check", &["--cert", cert.to_str().expect("temp path")]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    let certificate = std::fs::read(&cert).expect("read fresh edit-distance certificate");
    for (input, expected) in [
        ("kitten\nsitting", "3"),
        ("abc\nabc", "0"),
        ("\nabcdefghij", "10"),
    ] {
        let output = project.cli(
            "run",
            &[
                "--input",
                input,
                "--cert",
                cert.to_str().expect("temp path"),
            ],
        );
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert_eq!(envelope(&output)["data"]["output_text"], expected);
        let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["run", "--package"])
            .arg(&project.root)
            .args(["--input", input])
            .output()
            .expect("run human-output edit-distance CLI");
        assert!(output.status.success());
        assert_eq!(output.stdout, expected.as_bytes());
    }
    assert_eq!(
        std::fs::read(&cert).expect("read supplied certificate"),
        certificate
    );
    let output = project.cli("run", &["--input", "kitten\nsitting", "--fuel", "1"]);
    assert!(!output.status.success());
    assert_eq!(
        envelope(&output)["diagnostics"][0]["code"],
        concat!("R", "801")
    );
}

#[cfg(feature = "solver")]
#[test]
fn migrated_tool_preserves_outputs_on_the_production_runtime() {
    let project = Project::new();
    project.lock();
    let package = sigil_compiler::package::compile_local_package_with_context(
        &project.root,
        sigil_compiler::CompileOptions::default(),
        &sigil_compiler::CompilerContext::default(),
    )
    .expect("solver compile real graph");
    let before = sigil_compiler::compile_named_module(
        "split_count_before.sigil",
        include_str!("../../../tools/task018_split_count.sigil"),
    )
    .expect("compile before fixture");
    let mut cases = vec![
        vec![],
        b"alpha".to_vec(),
        b",".to_vec(),
        b",a,,b,".to_vec(),
        b"a\0b,c".to_vec(),
        "α,β,γ".as_bytes().to_vec(),
        vec![44; 9],
        vec![44; 99],
        vec![44; 999],
    ];
    // Also exercise arbitrary bytes rather than only valid UTF-8.
    cases.push(vec![255, 0, 44, 128, 44]);
    for input in cases {
        let expected = if input.is_empty() {
            0
        } else {
            1 + input.iter().filter(|byte| **byte == 44).count()
        };
        for wasm in [&before.wasm_inner, &package.compilation.wasm_inner] {
            let output = sigil_runtime::execute_ephemeral_with_budgets(
                wasm,
                &input,
                100_000,
                10_000_000,
                16 * 1024 * 1024,
                &sigil_runtime::IoGrants::default(),
            )
            .expect("bounded runtime execution");
            assert_eq!(output.output, expected.to_string().as_bytes());
        }
    }
    let output = project.cli("run", &["--input", "alpha,beta,gamma"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(envelope(&output)["data"]["output_text"], "3");
    let output = project.cli("run", &["--input", "a,b", "--fuel", "1"]);
    assert!(!output.status.success());
    assert_eq!(
        envelope(&output)["diagnostics"][0]["code"],
        concat!("R", "801")
    );
}

#[cfg(feature = "solver")]
#[test]
fn package_check_run_and_supplied_certificate_round_trip_without_overwrite() {
    let project = Project::new();
    project.lock();
    let cert = project.directory.join("certificate.json");
    let wasm = project.directory.join("tool.wasm");
    let output = project.cli(
        "check",
        &[
            "--cert",
            cert.to_str().expect("temp path"),
            "--emit-wasm",
            wasm.to_str().expect("temp path"),
        ],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(wasm.is_file());
    let original = std::fs::read(&cert).expect("read graph certificate");
    let output = project.cli(
        "run",
        &[
            "--cert",
            cert.to_str().expect("temp path"),
            "--input",
            "a,b",
        ],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(envelope(&output)["data"]["output_text"], "2");
    assert_eq!(
        std::fs::read(&cert).expect("read preserved certificate"),
        original
    );
    let mut value: serde_json::Value =
        serde_json::from_slice(&original).expect("decode certificate");
    value["package_graph_hash"] = format!("sha256:{}", "0".repeat(64)).into();
    std::fs::write(&cert, serde_json::to_vec(&value).expect("encode mismatch"))
        .expect("write mismatch");
    let output = project.cli("run", &["--cert", cert.to_str().expect("temp path")]);
    assert!(!output.status.success());
    // The exact comparator refusal, carried in `data`: a mismatching graph hash
    // must be rejected by the certificate comparison, not by a cert-file shape
    // guard or the solver gate, which also answer `status: error`.
    let refusal = envelope(&output);
    assert_eq!(refusal["status"], "error");
    assert_eq!(refusal["data"]["code"], "E_CERTIFICATE", "{refusal}");
}

#[cfg(feature = "solver")]
#[test]
fn non_public_entry_and_missing_root_entry_cannot_run() {
    for (source, contract) in [
        (
            "module tool; pub fn tool_main(p:i64,n:i64)->i64 @Internal ! {Alloc} { let out=alloc(1); store8(out,48); return out*4294967296+1; }",
            "tool::tool_main(p:Public,n:Public)->Internal",
        ),
        (
            "module tool; pub fn other()->i64 ! {Alloc} { return alloc(1); }",
            "tool::other()->Public",
        ),
    ] {
        let project = Project::new();
        std::fs::write(project.root.join("src/tool.sigil"), source)
            .expect("write unsupported entry");
        project.edit_manifest(|value| {
            value["declared"]["taint_contracts"] = serde_json::json!([contract])
        });
        project.lock();
        let output = project.cli("run", &[]);
        assert!(!output.status.success());
        assert_eq!(
            envelope(&output)["diagnostics"][0]["code"],
            concat!("R", "800"),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
    }
}

#[test]
fn cli_source_selection_matches_the_compiler_api() {
    let project = Project::new();
    let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["package-lock", "--root"])
        .arg(&project.root)
        .arg("--dependency")
        .arg(format!("sigil/fmt={}", project.dependency.display()))
        .arg("--json")
        .output()
        .expect("invoke explicit-source lock command");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(envelope(&output)["data"]["admission"], "not_evaluated");
    assert!(load_graph(&project.root).is_ok());
}
