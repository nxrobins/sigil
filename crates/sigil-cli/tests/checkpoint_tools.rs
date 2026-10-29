//! WHY THIS TEST EXISTS. Resumption needs compatible complete state and failed
//! publication must retain its predecessor. Exercise canonical envelopes and the
//! existing grant-controlled KV host separately, without widening package-run.
#![cfg(unix)]

use sigil_compiler::package::{
    LocalPackageDependency, create_local_package_lock_with_dependencies,
};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
static SEQUENCE: AtomicU64 = AtomicU64::new(0);
fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}
fn json(path: &Path) -> serde_json::Value {
    serde_json::from_slice(&std::fs::read(path).expect("artifact")).expect("JSON")
}
fn hash(bytes: &[u8]) -> String {
    format!(
        "sha256:{}",
        ring::digest::digest(&ring::digest::SHA256, bytes)
            .as_ref()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>()
    )
}
fn copy(source: &Path, target: &Path) {
    std::fs::create_dir_all(target).expect("owned directory");
    for entry in std::fs::read_dir(source).expect("package") {
        let entry = entry.expect("entry");
        if [".sigil", "sigil-package.lock.json", "__pycache__"]
            .iter()
            .any(|n| entry.file_name() == *n)
        {
            continue;
        }
        let kind = entry.file_type().expect("type");
        if kind.is_dir() {
            copy(&entry.path(), &target.join(entry.file_name()));
        } else {
            assert!(kind.is_file());
            std::fs::copy(entry.path(), target.join(entry.file_name())).expect("copy");
        }
    }
}
struct Fixture {
    directory: PathBuf,
    root: PathBuf,
    storage: bool,
}
impl Fixture {
    fn names(&self) -> Vec<&'static str> {
        if self.storage {
            vec!["kv", "storage"]
        } else {
            vec!["json", "records", "checkpoint"]
        }
    }
    fn dependency(&self, name: &str) -> LocalPackageDependency {
        LocalPackageDependency {
            package: format!("sigil/{name}"),
            path: self.directory.join(name),
        }
    }
    fn new(storage: bool) -> Self {
        let directory = loop {
            let path = std::env::temp_dir().join(format!(
                "sigil-checkpoint-{}-{}",
                std::process::id(),
                SEQUENCE.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => break path,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("owned root: {e}"),
            }
        };
        let root = directory.join("consumer");
        std::fs::create_dir_all(root.join("src")).expect("root source");
        let fixture = Self {
            directory,
            root,
            storage,
        };
        let names = fixture.names();
        for name in &names {
            copy(
                &repo().join("library/packages").join(name),
                &fixture.directory.join(name),
            );
        }
        let mut dependencies = Vec::new();
        for (index, name) in names.iter().enumerate() {
            let selected = names[..index]
                .iter()
                .map(|n| fixture.dependency(n))
                .collect::<Vec<_>>();
            let graph: serde_json::Value = serde_json::from_slice(
                &create_local_package_lock_with_dependencies(
                    &fixture.directory.join(name),
                    &selected,
                )
                .expect("provider graph"),
            )
            .expect("graph");
            let pin = graph["nodes"]
                .as_array()
                .expect("nodes")
                .iter()
                .find(|n| n["package"] == format!("sigil/{name}"))
                .expect("provider")["content_hash"]
                .clone();
            dependencies.push(serde_json::json!({"package":format!("sigil/{name}"),"requirement":"=0.1.0-public.1","source":"workspace","content_hash":pin,"features":[],"default_features":false,"optional":false}));
        }
        dependencies.sort_by_key(|d| d["package"].as_str().expect("name").to_string());
        let mut manifest = json(&repo().join("library/programs/autoresearch/sigil-package.json"));
        manifest["namespace"] = "checkpoint-probe".into();
        manifest["modules"] = serde_json::json!(["tool"]);
        manifest["dependencies"] = dependencies.into();
        manifest["declared"]["taint_contracts"] = serde_json::json!([if storage {
            "tool::tool_main(input_ptr:Public,input_len:Public)->Internal"
        } else {
            "tool::tool_main(input_ptr:Public,input_len:Public)->Public"
        }]);
        if storage {
            manifest["declared"]["rings"] = serde_json::json!(["trusted_outer"]);
            manifest["declared"]["trusted_surface"] = serde_json::json!(["module:tool"]);
            manifest["declared"]["effects"] = serde_json::json!(["Alloc", "FFI", "KvIO", "Unsafe"]);
            manifest["declared"]["grant_categories"] = serde_json::json!(["ffi"]);
        }
        std::fs::write(
            fixture.root.join("sigil-package.json"),
            serde_json::to_vec(&manifest).expect("manifest"),
        )
        .expect("write");
        std::fs::write(
            fixture.root.join("src/tool.sigil"),
            "module tool;pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {Alloc} {return 0;}",
        )
        .expect("bootstrap");
        fixture
    }
    fn lock(&self) -> Vec<u8> {
        create_local_package_lock_with_dependencies(
            &self.root,
            &self
                .names()
                .iter()
                .map(|n| self.dependency(n))
                .collect::<Vec<_>>(),
        )
        .expect("root graph")
    }
    #[cfg(feature = "solver")]
    fn probe(storage: bool, body: &str) -> Self {
        let fixture = Self::new(storage);
        let header = if storage {
            "#[ring(outer)] #[trusted] module tool;use sigil::storage;pub fn tool_main(input_ptr:i64,input_len:i64)->i64 @Internal ! {KvIO,Alloc,FFI,Unsafe}"
        } else {
            "module tool;use sigil::checkpoint;use sigil::records;pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {Alloc}"
        };
        std::fs::write(
            fixture.root.join("src/tool.sigil"),
            format!("{header} {{{body}}}"),
        )
        .expect("probe");
        fixture
    }
    #[cfg(feature = "solver")]
    fn compile(&self) -> sigil_compiler::package::PackageCompilation {
        self.lock();
        let context = if self.storage {
            sigil_compiler::CompilerContext::with_host_profile(
                sigil_runtime::ephemeral_host_profile(),
            )
        } else {
            sigil_compiler::CompilerContext::default()
        };
        sigil_compiler::package::compile_local_package_with_context(
            &self.root,
            sigil_compiler::CompileOptions::default(),
            &context,
        )
        .expect("solver graph")
    }
    #[cfg(feature = "solver")]
    fn mutate(&self, needle: &str, replacement: &str) {
        let name = if self.storage {
            "storage"
        } else {
            "checkpoint"
        };
        let path = self.directory.join(name).join(format!("src/{name}.sigil"));
        let source = std::fs::read_to_string(&path).expect("source");
        assert_eq!(source.matches(needle).count(), 1);
        std::fs::write(path, source.replacen(needle, replacement, 1)).expect("owned mutant");
        let old = self.directory.join(name).join("sigil-package.lock.json");
        std::fs::rename(&old, old.with_extension("prior")).expect("preserve owned lock");
        let selected = self
            .names()
            .into_iter()
            .filter(|n| *n != name)
            .map(|n| self.dependency(n))
            .collect::<Vec<_>>();
        let graph: serde_json::Value = serde_json::from_slice(
            &create_local_package_lock_with_dependencies(&self.directory.join(name), &selected)
                .expect("changed provider"),
        )
        .expect("graph");
        let pin = graph["nodes"]
            .as_array()
            .expect("nodes")
            .iter()
            .find(|n| n["package"] == format!("sigil/{name}"))
            .expect("provider")["content_hash"]
            .clone();
        let path = self.root.join("sigil-package.json");
        let mut manifest = json(&path);
        manifest["dependencies"]
            .as_array_mut()
            .expect("deps")
            .iter_mut()
            .find(|d| d["package"] == format!("sigil/{name}"))
            .expect("pin")["content_hash"] = pin;
        std::fs::write(path, serde_json::to_vec(&manifest).expect("encode")).expect("repin mutant");
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

#[test]
fn checkpoint_storage_metadata_and_original_kv_are_bound() {
    let original = std::fs::read(repo().join("stdlib/sigil/kv.sigil")).expect("original");
    let mut packaged =
        std::fs::read(repo().join("library/packages/kv/src/kv.sigil")).expect("copy");
    assert_eq!(original, packaged);
    packaged.push(b'!');
    assert_ne!(original, packaged);
    for name in ["checkpoint", "storage", "kv"] {
        let root = repo().join("library/packages").join(name);
        let manifest = json(&root.join("sigil-package.json"));
        for (field, file) in [
            ("api_card_hash", "api-card.json"),
            ("api_contract_hash", "API.md"),
            ("charter_hash", "README.md"),
            ("evidence_manifest_hash", "inputs.json"),
        ] {
            assert_eq!(
                manifest["evidence"][field],
                hash(&std::fs::read(root.join(file)).expect("file"))
            );
        }
        for (file, expected) in json(&root.join("inputs.json"))["files"]
            .as_object()
            .expect("inventory")
        {
            let mut bytes = std::fs::read(root.join(file)).expect("input");
            assert_eq!(expected, &hash(&bytes));
            bytes.push(0);
            assert_ne!(expected, &hash(&bytes));
        }
    }
    for storage in [false, true] {
        let fixture = Fixture::new(storage);
        let lock: serde_json::Value = serde_json::from_slice(&fixture.lock()).expect("lock");
        assert_eq!(
            lock["nodes"].as_array().expect("nodes").len(),
            if storage { 3 } else { 4 }
        );
    }
}

#[cfg(feature = "solver")]
fn literal(name: &str, bytes: &[u8]) -> String {
    let mut source = format!("let {name}=alloc({});", bytes.len());
    for (i, b) in bytes.iter().enumerate() {
        source.push_str(&format!("store8({name}+{i},{b});"));
    }
    source
}
#[cfg(feature = "solver")]
fn identity() -> String {
    literal("domain", b"job-42") + &literal("compatibility", b"search-f64-v1")
}
#[cfg(feature = "solver")]
fn initialize() -> Fixture {
    Fixture::probe(
        false,
        &(identity()
            + "return checkpoint::initialize(domain,6,compatibility,13,input_ptr,input_len);"),
    )
}
#[cfg(feature = "solver")]
fn opener() -> Fixture {
    Fixture::probe(
        false,
        &(identity()
            + "let snap=checkpoint::open(input_ptr,input_len,domain,6,compatibility,13);if snap.error<0 {return snap.error;}return snap.current*4294967296+snap.current_len;"),
    )
}
#[cfg(feature = "solver")]
fn advancer(revision: u64) -> Fixture {
    Fixture::probe(false, &format!("{}let mut n=0;while n<input_len && load8(input_ptr+n)!=10 {{n=n+1;}}if n==input_len {{return -400;}}
        return checkpoint::advance(input_ptr,n,domain,6,compatibility,13,{revision},input_ptr+n+1,input_len-n-1);",identity()))
}
#[cfg(feature = "solver")]
fn execute(
    package: &sigil_compiler::package::PackageCompilation,
    input: &[u8],
    grants: &sigil_runtime::IoGrants,
) -> Result<sigil_runtime::ToolResult, sigil_runtime::ToolError> {
    let wasm = package
        .compilation
        .wasm_outer
        .as_ref()
        .unwrap_or(&package.compilation.wasm_inner);
    sigil_runtime::execute_ephemeral_with_budgets(
        wasm,
        input,
        500_000,
        10_000_000,
        16 * 1024 * 1024,
        grants,
    )
}
#[cfg(feature = "solver")]
fn pure(package: &sigil_compiler::package::PackageCompilation, input: &[u8]) -> Vec<u8> {
    execute(package, input, &sigil_runtime::IoGrants::none())
        .expect("native checkpoint")
        .output
}
#[cfg(feature = "solver")]
fn refusal(result: Result<sigil_runtime::ToolResult, sigil_runtime::ToolError>, code: i64) {
    assert!(
        matches!(&result,Err(sigil_runtime::ToolError::Trapped {message}) if message==&format!("tool returned error ({code})")),
        "{result:?}"
    );
}
#[cfg(feature = "solver")]
fn stage_input(old: &[u8], next: &[u8]) -> Vec<u8> {
    [old, b"\n", next].concat()
}

#[cfg(feature = "solver")]
#[test]
fn checkpoint_round_trip_revision_and_previous_payload_are_exact() {
    let init = initialize();
    let init = init.compile();
    let open = opener();
    let open = open.compile();
    let stage = advancer(0);
    let stage = stage.compile();
    for current in [b"".as_slice(), b"first", b"\x00\xff\n\"\\"] {
        let first = pure(&init, current);
        assert_eq!(pure(&open, &first), current);
        let parsed: serde_json::Value = serde_json::from_slice(&first).expect("JSON");
        assert_eq!(parsed["revision"], "0000000000000000");
        assert_eq!(parsed["previous_hex"], "");
        let second = pure(&stage, &stage_input(&first, b"next"));
        assert_eq!(pure(&open, &second), b"next");
        let parsed: serde_json::Value = serde_json::from_slice(&second).expect("JSON");
        assert_eq!(
            parsed["previous_hex"],
            current
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        );
        assert_eq!(parsed["revision"], "0000000000000001");
        refusal(
            execute(
                &stage,
                &stage_input(&second, b"stale"),
                &sigil_runtime::IoGrants::none(),
            ),
            409,
        );
        assert_eq!(
            pure(&open, &first),
            current,
            "the prior snapshot remains usable"
        );
    }
    let first = pure(&init, b"preserve me");
    for (revision, next, code) in [
        (0, b"new".to_vec(), 0),
        (1, b"new".to_vec(), -409),
        (0, vec![0; 4097], -413),
    ] {
        let body=format!("{}let mut n=0;while n<input_len && load8(input_ptr+n)!=10 {{n=n+1;}}
            let result=checkpoint::advance(input_ptr,n,domain,6,compatibility,13,{revision},input_ptr+n+1,input_len-n-1);
            if {code}<0 {{if result!={code} {{return -1;}}}}else{{if result<0 {{return result;}}}}
            return input_ptr*4294967296+n;",identity());
        let fixture = Fixture::probe(false, &body);
        assert_eq!(
            pure(&fixture.compile(), &stage_input(&first, &next)),
            first,
            "observe prior bytes in the same execution"
        );
    }
}

#[cfg(feature = "solver")]
#[test]
fn checkpoint_refuses_noncanonical_incompatible_and_oversized_states() {
    let init = initialize();
    let init = init.compile();
    let open = opener();
    let open = open.compile();
    let first = pure(&init, b"first");
    let text = String::from_utf8(first.clone()).expect("ASCII");
    let bad = [
        (text.replace("job-42", "job-43"), 409),
        (text.replace("search-f64-v1", "search-f64-v2"), 409),
        (
            text.replace("sigil-checkpoint-v1", "sigil-checkpoint-v2"),
            422,
        ),
        (text.replace("0000000000000000", "0000000100000000"), 413),
        (text.replace("6669727374", "GG69727374"), 422),
        (
            text.replace("\"previous_hex\":\"\"", "\"previous_hex\":\"ff\""),
            422,
        ),
        (text.replacen('{', "{\"extra\":0,", 1), 422),
        (
            text.replacen('{', "{\"format\":\"sigil-checkpoint-v1\",", 1),
            422,
        ),
        (format!(" {text}"), 422),
        (format!("{text}!"), 400),
        (
            text.replace("\"previous_hex\":\"\"", "\"absent\":\"\""),
            404,
        ),
    ];
    for (value, code) in bad {
        refusal(
            execute(&open, value.as_bytes(), &sigil_runtime::IoGrants::none()),
            code,
        );
    }
    let maximum = vec![0xa5; 4096];
    let first = pure(&init, &maximum);
    assert_eq!(pure(&open, &first), maximum);
    let stage = advancer(0);
    let stage = stage.compile();
    let second = pure(&stage, &stage_input(&first, &maximum));
    assert_eq!(pure(&open, &second), maximum);
    let next = advancer(1);
    let next = next.compile();
    let third = pure(&next, &stage_input(&second, &maximum));
    assert_eq!(pure(&open, &third), maximum);
    println!("maximum checkpoint {} bytes", second.len());
    refusal(
        execute(&init, &vec![0; 4097], &sigil_runtime::IoGrants::none()),
        413,
    );
    refusal(
        execute(
            &stage,
            &stage_input(&first, &vec![0; 4097]),
            &sigil_runtime::IoGrants::none(),
        ),
        413,
    );
    let overflow = advancer(4294967295);
    let overflow = overflow.compile();
    let last = text.replace("0000000000000000", "00000000ffffffff");
    assert_eq!(pure(&open, last.as_bytes()), b"first");
    refusal(
        execute(
            &overflow,
            &stage_input(last.as_bytes(), b"next"),
            &sigil_runtime::IoGrants::none(),
        ),
        413,
    );
}

#[cfg(feature = "solver")]
fn storage_body(write: bool) -> String {
    let ids = literal("ns", b"search") + &literal("key", b"job-42");
    if !write {
        return ids + "return storage::load(ns,6,key,6);";
    }
    ids + "if input_len<4 {return -400;}let n=load8(input_ptr)+256*load8(input_ptr+1)+65536*load8(input_ptr+2)+16777216*load8(input_ptr+3);if n>input_len-4 {return -400;}return storage::publish(ns,6,key,6,input_ptr+4,n,input_ptr+4+n,input_len-4-n);"
}
#[cfg(feature = "solver")]
fn publication(expected: &[u8], next: &[u8]) -> Vec<u8> {
    [
        (expected.len() as u32).to_le_bytes().as_slice(),
        expected,
        next,
    ]
    .concat()
}
#[cfg(feature = "solver")]
fn grants(root: &Path, read: bool, write: bool) -> sigil_runtime::IoGrants {
    sigil_runtime::IoGrants {
        kv: if read {
            vec![sigil_runtime::KvGrant {
                namespace: "search".into(),
                root: root.to_path_buf(),
            }]
        } else {
            vec![]
        },
        kv_write: if write {
            vec![sigil_runtime::KvWriteGrant {
                namespace: "search".into(),
                root: root.to_path_buf(),
            }]
        } else {
            vec![]
        },
        ..Default::default()
    }
}

#[cfg(feature = "solver")]
#[test]
fn checkpoint_publication_round_trips_and_refusals_preserve_storage() {
    let init = initialize();
    let init = init.compile();
    let first = pure(&init, b"first");
    let stage = advancer(0);
    let stage = stage.compile();
    let second = pure(&stage, &stage_input(&first, b"next"));
    let writer = Fixture::probe(true, &storage_body(true));
    let write = writer.compile();
    let reader = Fixture::probe(true, &storage_body(false));
    let read = reader.compile();
    let store = writer.directory.join("store");
    std::fs::create_dir(&store).expect("owned storage");
    let rw = grants(&store, true, true);
    let ro = grants(&store, true, false);
    let wo = grants(&store, false, true);
    refusal(execute(&read, b"", &rw), 404);
    refusal(execute(&write, &publication(b"", &first), &wo), 403);
    refusal(execute(&write, &publication(b"", &first), &ro), 403);
    assert!(
        execute(&write, &publication(b"", &first), &rw)
            .expect("initialize publication")
            .output
            .is_empty()
    );
    assert_eq!(execute(&read, b"", &ro).expect("restored").output, first);
    refusal(execute(&write, &publication(b"", &second), &rw), 409);
    refusal(
        execute(&write, &publication(b"wrong prior", &second), &rw),
        409,
    );
    refusal(execute(&write, &publication(&first, &second), &ro), 403);
    let mut broken = grants(&store, true, true);
    broken.kv_write[0].root = writer.directory.join("missing-write-root");
    refusal(execute(&write, &publication(&first, &second), &broken), 500);
    assert_eq!(
        execute(&read, b"", &ro)
            .expect("preserved after failure")
            .output,
        first
    );
    assert!(
        execute(&write, &publication(&first, &second), &rw)
            .expect("advance publication")
            .output
            .is_empty()
    );
    refusal(execute(&write, &publication(&first, &second), &rw), 409);
    assert_eq!(
        execute(&read, b"", &ro).expect("new snapshot").output,
        second
    );
    refusal(execute(&read, b"", &sigil_runtime::IoGrants::none()), 403);
    let mut wrong = grants(&store, true, true);
    wrong.kv[0].namespace = "other".into();
    wrong.kv_write[0].namespace = "other".into();
    refusal(execute(&write, &publication(&second, &first), &wrong), 403);
    refusal(execute(&write, &publication(&second, b""), &rw), 400);
    refusal(
        execute(&write, &publication(&second, &vec![0; 32769]), &rw),
        413,
    );
    assert_eq!(execute(&read, b"", &ro).expect("preserved").output, second);
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["run", "--package"])
        .arg(&writer.root)
        .args(["--host-profile", "ephemeral", "--json"])
        .output()
        .expect("closed package-run gate");
    assert!(!output.status.success());
    let error: serde_json::Value = serde_json::from_slice(&output.stdout).expect("envelope");
    let codes = error["diagnostics"]
        .as_array()
        .expect("diagnostics")
        .iter()
        .map(|d| d["code"].as_str().expect("code"))
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        codes,
        std::collections::BTreeSet::from([concat!("R", "800")])
    );
}

#[cfg(feature = "solver")]
#[test]
fn checkpoint_live_revision_canonical_and_publication_faults_are_detected() {
    let init = initialize();
    let init = init.compile();
    let first = pure(&init, b"first");
    let clean = advancer(0);
    let clean = clean.compile();
    let second = pure(&clean, &stage_input(&first, b"next"));
    let mutant = advancer(0);
    mutant.mutate(
        "if old.revision != expected_revision { return -409; } else {}",
        "if false { return -409; } else {}",
    );
    assert!(
        execute(
            &mutant.compile(),
            &stage_input(&second, b"stale"),
            &sigil_runtime::IoGrants::none()
        )
        .is_ok()
    );
    refusal(
        execute(
            &clean,
            &stage_input(&second, b"stale"),
            &sigil_runtime::IoGrants::none(),
        ),
        409,
    );
    let changed =
        String::from_utf8(first.clone())
            .expect("ASCII")
            .replacen('{', "{\"extra\":0,", 1);
    let open = opener();
    let open = open.compile();
    refusal(
        execute(&open, changed.as_bytes(), &sigil_runtime::IoGrants::none()),
        422,
    );
    let mutant = opener();
    mutant.mutate(
        "if !canonical(ptr, len, head, c, p) { return failed(-422); } else {}",
        "if false { return failed(-422); } else {}",
    );
    assert_eq!(pure(&mutant.compile(), changed.as_bytes()), b"first");
    let writer = Fixture::probe(true, &storage_body(true));
    let write = writer.compile();
    let reader = Fixture::probe(true, &storage_body(false));
    let read = reader.compile();
    let store = writer.directory.join("store");
    std::fs::create_dir(&store).expect("owned");
    let rw = grants(&store, true, true);
    execute(&write, &publication(b"", &first), &rw).expect("positive control");
    let mut different = first.clone();
    different[2] ^= 1;
    refusal(execute(&write, &publication(&different, &second), &rw), 409);
    let mutant = Fixture::probe(true, &storage_body(true));
    mutant.mutate(
        "if load8(ptr + i) != load8(expected + i) { return -409; } else {}",
        "if false { return -409; } else {}",
    );
    execute(&mutant.compile(), &publication(&different, &second), &rw)
        .expect("live stale-publication fault");
    assert_eq!(
        execute(&read, b"", &rw).expect("fault observed").output,
        second
    );
}

#[cfg(feature = "solver")]
#[test]
fn checkpoint_labels_host_profile_and_resource_limits_remain_closed() {
    for (label, output, accepted) in [
        ("Public", "Public", true),
        ("Internal", "Internal", true),
        ("Secret", "Secret", true),
        ("Internal", "Public", false),
        ("Secret", "Internal", false),
    ] {
        let fixture = Fixture::new(false);
        let source = format!(
            "module tool;use sigil::checkpoint;
            fn sample(ptr:i64 @{label},len:i64 @{label})->i64 @{output} ! {{Alloc}} {{
                {}return checkpoint::initialize(domain,6,compatibility,13,ptr,len);}}
            pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return 0;}}",
            identity()
        );
        std::fs::write(fixture.root.join("src/tool.sigil"), source).expect("label probe");
        fixture.lock();
        let result = sigil_compiler::package::compile_local_package_with_context(
            &fixture.root,
            sigil_compiler::CompileOptions::default(),
            &sigil_compiler::CompilerContext::default(),
        );
        if accepted {
            assert!(result.is_ok(), "{label} must retain its label");
        } else {
            let Err(sigil_compiler::package::PackageCompileError::Compiler(error)) = result else {
                panic!("must fail in taint checking")
            };
            let codes = error
                .diagnostics()
                .iter()
                .map(|d| d.code().to_string())
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(
                codes,
                std::collections::BTreeSet::from([concat!("T", "001").to_string()])
            );
        }
    }
    let fixture = initialize();
    let package = fixture.compile();
    assert!(!pure(&package, b"control").is_empty());
    for (fuel, engine, memory) in [
        (1, 10_000_000, 16 * 1024 * 1024),
        (500_000, 1, 16 * 1024 * 1024),
        (500_000, 10_000_000, 1),
    ] {
        assert!(
            sigil_runtime::execute_ephemeral_with_budgets(
                &package.compilation.wasm_inner,
                b"control",
                fuel,
                engine,
                memory,
                &sigil_runtime::IoGrants::none()
            )
            .is_err()
        );
    }
    let writer = Fixture::probe(true, &storage_body(true));
    writer.lock();
    let unbound = sigil_compiler::package::compile_local_package_with_context(
        &writer.root,
        sigil_compiler::CompileOptions::default(),
        &sigil_compiler::CompilerContext::default(),
    );
    let Err(sigil_compiler::package::PackageCompileError::Compiler(error)) = unbound else {
        panic!("host profile fails during checking")
    };
    let codes = error
        .diagnostics()
        .iter()
        .map(|d| d.code().to_string())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        codes,
        std::collections::BTreeSet::from([concat!("I", "013").to_string()])
    );
    let bound = sigil_compiler::package::compile_local_package_with_context(
        &writer.root,
        sigil_compiler::CompileOptions::default(),
        &sigil_compiler::CompilerContext::with_host_profile(sigil_runtime::ephemeral_host_profile()),
    );
    assert!(
        bound.is_ok(),
        "explicit existing profile is the accept twin"
    );
}
