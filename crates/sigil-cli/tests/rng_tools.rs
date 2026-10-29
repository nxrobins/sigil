//! WHY THIS TEST EXISTS. Reproducible search needs an actual reference stream,
//! unbiased bounded mapping, exact snapshots and unchanged state on refusal.
//! These tests execute imported SIGIL, including live faults and consumer replay.
#![cfg(unix)]

use sigil_compiler::package::{
    LocalPackageDependency, create_local_package_lock_with_dependencies,
};
use std::path::{Path, PathBuf};
use std::process::Command;
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
        if [".sigil", "__pycache__", "sigil-package.lock.json"]
            .iter()
            .any(|name| entry.file_name() == *name)
        {
            continue;
        }
        let kind = entry.file_type().expect("type");
        if kind.is_dir() {
            copy(&entry.path(), &target.join(entry.file_name()));
        } else {
            assert!(kind.is_file(), "no symlinks");
            std::fs::copy(entry.path(), target.join(entry.file_name())).expect("copy");
        }
    }
}
struct Fixture {
    directory: PathBuf,
    root: PathBuf,
    provider: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        let directory = loop {
            let directory = std::env::temp_dir().join(format!(
                "sigil-rng-{}-{}",
                std::process::id(),
                SEQUENCE.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&directory) {
                Ok(()) => break directory,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("owned fixture: {e}"),
            }
        };
        let root = directory.join("consumer");
        let provider = directory.join("rng");
        copy(&repo().join("library/programs/autoresearch-propose"), &root);
        copy(&repo().join("library/packages/rng"), &provider);
        Self {
            directory,
            root,
            provider,
        }
    }
    fn lock(&self) -> Vec<u8> {
        create_local_package_lock_with_dependencies(
            &self.root,
            &[LocalPackageDependency {
                package: "sigil/rng".into(),
                path: self.provider.clone(),
            }],
        )
        .expect("fresh graph")
    }
    #[cfg(feature = "solver")]
    fn compile(&self) -> sigil_compiler::package::PackageCompilation {
        self.lock();
        sigil_compiler::package::compile_local_package_with_context(
            &self.root,
            sigil_compiler::CompileOptions::default(),
            &sigil_compiler::CompilerContext::default(),
        )
        .expect("solver graph")
    }
    #[cfg(feature = "solver")]
    fn probe(body: &str) -> Self {
        let f = Self::new();
        std::fs::write(f.root.join("src/tool.sigil"), format!(
            "module tool;use sigil::rng;use sigil::vec;pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{
            let observations:Vec<u64> = Vec::with_capacity(256);
            {body}
            let blob=alloc(observations.len()*8);let mut j=0;
            while j<observations.len()*8 {{store8(blob+j,load8(observations.buf+j));j=j+1;}}
            return blob*4294967296+observations.len()*8;}}"
        )).expect("probe");
        f
    }
    #[cfg(feature = "solver")]
    fn mutate(&self, needle: &str, replacement: &str) {
        let path = self.provider.join("src/rng.sigil");
        let source = std::fs::read_to_string(&path).expect("provider");
        assert_eq!(source.matches(needle).count(), 1, "unique mutation site");
        std::fs::write(path, source.replacen(needle, replacement, 1)).expect("mutant");
        let derived: serde_json::Value = serde_json::from_slice(
            &sigil_compiler::package::derive_local_package_lock(&self.provider).expect("identity"),
        )
        .expect("JSON");
        let mut manifest = json(&self.root.join("sigil-package.json"));
        manifest["dependencies"][0]["content_hash"] = derived["nodes"][0]["content_hash"].clone();
        std::fs::write(
            self.root.join("sigil-package.json"),
            serde_json::to_vec(&manifest).expect("encode"),
        )
        .expect("owned pin");
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

#[test]
fn rng_inputs_reference_and_consumer_graph_are_bound() {
    for (directory, inventory) in [
        ("library/packages/rng", "inputs.json"),
        ("library/programs/autoresearch-propose", "tool-inputs.json"),
    ] {
        let root = repo().join(directory);
        let manifest = json(&root.join("sigil-package.json"));
        for (field, file) in [
            ("api_card_hash", "api-card.json"),
            ("api_contract_hash", "API.md"),
            ("charter_hash", "README.md"),
            ("evidence_manifest_hash", inventory),
        ] {
            assert_eq!(
                manifest["evidence"][field],
                hash(&std::fs::read(root.join(file)).expect("file"))
            );
        }
        for (file, expected) in json(&root.join(inventory))["files"]
            .as_object()
            .expect("inventory")
        {
            let mut data = std::fs::read(root.join(file)).expect("file");
            assert_eq!(expected, &hash(&data));
            data.push(b'!');
            assert_ne!(expected, &hash(&data), "live drift");
        }
    }
    let references = repo().join("library/tests/fixtures/rng");
    let reference = json(&references.join("pcg-v1.json"));
    assert_eq!(reference["cases"].as_array().expect("cases").len(), 30);
    let actual = reference["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .map(|case| {
            (
                case["seed"].as_u64().expect("seed"),
                case["stream"].as_u64().expect("stream"),
                case["bound"].as_u64().expect("bound"),
            )
        })
        .collect::<std::collections::BTreeSet<_>>();
    let expected = [
        (42, 54),
        (0, 0),
        (1, 1),
        (u64::MAX, u64::MAX / 2),
        (1_u64 << 63, 17),
    ]
    .into_iter()
    .flat_map(|(seed, stream)| {
        [0, 1, 6, 2147483649, 4294967295, 4294967296].map(|bound| (seed, stream, bound))
    })
    .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(
        actual, expected,
        "reference matrix; regenerate with SIGIL_REGENERATE_RNG=1 python3 library/tests/fixtures/rng/generate.py"
    );
    for (file, expected) in reference["sources"].as_object().expect("source hashes") {
        assert_eq!(
            format!("sha256:{}", expected.as_str().expect("hash")),
            hash(&std::fs::read(references.join(file)).expect("reference"))
        );
    }
    let fixture = Fixture::new();
    let lock = fixture.lock();
    let graph: serde_json::Value = serde_json::from_slice(&lock).expect("graph");
    assert_eq!(graph["nodes"].as_array().expect("nodes").len(), 2);
    let provider = graph["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .find(|node| node["package"] == "sigil/rng")
        .expect("provider");
    let cached = fixture
        .root
        .join(provider["source"]["locator"].as_str().expect("cache"));
    std::fs::write(cached.join("src/rng.sigil"), "module rng;\n").expect("live drift");
    let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["check", "--package"])
        .arg(&fixture.root)
        .arg("--json")
        .output()
        .expect("check");
    assert!(!output.status.success());
    let result: serde_json::Value = serde_json::from_slice(&output.stdout).expect("JSON");
    assert_eq!(result["data"]["code"], "E_HASH_MISMATCH");
    assert_eq!(
        std::fs::read(fixture.root.join("sigil-package.lock.json")).expect("lock"),
        lock
    );
}

#[cfg(feature = "solver")]
fn execute(
    package: &sigil_compiler::package::PackageCompilation,
    input: &[u8],
) -> Result<sigil_runtime::ToolResult, sigil_runtime::ToolError> {
    sigil_runtime::execute_ephemeral_with_budgets(
        &package.compilation.wasm_inner,
        input,
        500_000,
        10_000_000,
        16 * 1024 * 1024,
        &sigil_runtime::IoGrants::none(),
    )
}
#[cfg(feature = "solver")]
fn observe(fixture: &Fixture) -> Vec<u64> {
    execute(&fixture.compile(), b"")
        .expect("probe")
        .output
        .as_chunks::<8>()
        .0
        .iter()
        .map(|chunk| u64::from_le_bytes(*chunk))
        .collect()
}
#[cfg(feature = "solver")]
fn stream_body(case: &serde_json::Value) -> String {
    let seed = case["seed"].as_u64().expect("seed");
    let draw = if case["bound"] == 0 {
        "rng::next(g)".to_owned()
    } else {
        format!("rng::below(g,{})", case["bound"])
    };
    format!(
        "let high:u64={};let seed:u64=high*4294967296+{};
        let g=rng::new(seed,{});observations.push(g.value);observations.push(g.increment);
        let before=alloc(0);let mut i=0;while i<12 {{
        let value={draw};if value<0 {{return value;}}
        observations.push(value.as_u64());observations.push(g.value);i=i+1;}}
        if alloc(0)!=before {{return -500;}}",
        seed >> 32,
        seed & 0xffff_ffff,
        case["stream"]
    )
}
#[cfg(feature = "solver")]
#[test]
fn rng_matches_pinned_c_reference_streams_bounds_and_allocation() {
    let reference = json(&repo().join("library/tests/fixtures/rng/pcg-v1.json"));
    for case in reference["cases"].as_array().expect("cases") {
        let fixture = Fixture::probe(&stream_body(case));
        let actual = observe(&fixture);
        let mut expected: Vec<u64> =
            serde_json::from_value(case["initial"].clone()).expect("words");
        for pair in case["draws"].as_array().expect("draws") {
            expected.extend(serde_json::from_value::<Vec<u64>>(pair.clone()).expect("draw"));
        }
        assert_eq!(actual, expected, "seed/stream/bound: {case}");
    }
}

#[cfg(feature = "solver")]
#[test]
fn rng_snapshot_and_invalid_calls_preserve_state_and_cells() {
    let source="let g=rng::new(42,54);let snap=rng::new_snapshot();
        let integer=rng::new_int();let unit=rng::new_float();
        let initial=g.value;let inc=g.increment;let before=alloc(0);
        if rng::snapshot_into(g,snap)!=0 {return -1;}
        let a=rng::below(g,2147483649);let b=rng::next(g);
        if rng::restore(g,snap)!=0 {return -2;}
        if rng::below(g,2147483649)!=a || rng::next(g)!=b {return -3;}
        if rng::restore(g,snap)!=0 {return -4;}
        integer.value=77;unit.value=0.5;
        if rng::below(g,0)!=-400 || rng::below(g,-1)!=-400 || rng::below(g,4294967297)!=-400 {return -5;}
        if rng::signed_into(g,-1,integer)!=-400 || rng::signed_into(g,2147483648,integer)!=-400 {return -6;}
        if g.value!=initial || g.increment!=inc || integer.value!=77 {return -7;}
        snap.version=2;if rng::restore(g,snap)!=-400 || g.value!=initial {return -8;}
        snap.version=1;snap.increment=2;
        if rng::restore(g,snap)!=-400 || g.value!=initial || g.increment!=inc {return -9;}
        g.error=-400;snap.value=7;
        if rng::next(g)!=-400 || rng::unit_into(g,unit)!=-400 || rng::snapshot_into(g,snap)!=-400 {return -10;}
        if snap.value!=7 || unit.value!=0.5 || g.value!=initial {return -11;}
        snap.increment=inc;snap.value=initial;
        if rng::restore(g,snap)!=0 || g.error!=0 {return -12;}
        g.increment=2;
        if rng::next(g)!=-400 || rng::signed_into(g,1,integer)!=-400 || integer.value!=77 {return -13;}
        if rng::restore(g,snap)!=0 || rng::signed_into(g,0,integer)!=0 || integer.value!=0 {return -14;}
        if rng::restore(g,snap)!=0 || rng::signed_into(g,2147483647,integer)!=0 {return -15;}
        if integer.value!=559678136 {return -16;}
        if rng::restore(g,snap)!=0 || rng::unit_into(g,unit)!=0 || unit.value!=2707161783.0/4294967296.0 {return -17;}
        if alloc(0)!=before {return -18;}
        observations.push(1);";
    assert_eq!(observe(&Fixture::probe(source)), vec![1]);
    let invalid = Fixture::probe(
        "let high:u64=9223372036854775807;let g=rng::new(0,high+1);
        if g.error!=-400 || rng::next(g)!=-400 {return -1;}
        let snap=rng::new_snapshot();if rng::restore(g,snap)!=0 {return -2;}
        observations.push(rng::next(g).as_u64());",
    );
    assert_eq!(observe(&invalid), vec![0]);
}

#[cfg(feature = "solver")]
#[test]
fn rng_live_faults_labels_and_retry_exhaustion_are_observed() {
    let reference = json(&repo().join("library/tests/fixtures/rng/pcg-v1.json"));
    let case = &reference["cases"][3]; // 2^31+1 rejects some real reference draws.
    let body = stream_body(case);
    let baseline = observe(&Fixture::probe(&body));
    for (needle, replacement) in [
        ("6364136223846793005", "6364136223846793007"),
        ("let rotation: u64 = value >> 59;", "let rotation: u64 = 0;"),
        (
            "let mixed: u64 = (exclusive >> 27) & 4294967295;",
            "let mixed: u64 = exclusive >> 27;",
        ),
        (
            "let threshold = (4294967296 - bound) % bound;",
            "let threshold = 0;",
        ),
    ] {
        let mutant = Fixture::probe(&body);
        mutant.mutate(needle, replacement);
        assert_ne!(observe(&mutant), baseline, "live fault {needle}");
    }
    let exhaustion = Fixture::probe(
        "let g=rng::new(42,54);let out=rng::new_int();out.value=88;
        let initial=g.value;let inc=g.increment;let before=alloc(0);
        let status=rng::below(g,2147483649);
        if status!=-429 || g.value!=initial || g.increment!=inc {return -1;}
        let status2=rng::signed_into(g,1073741824,out);
        if status2!=-429 || out.value!=88 || g.value!=initial || alloc(0)!=before {return -2;}
        observations.push(1);",
    );
    exhaustion.mutate("return bits.as_i64();", "return 0;");
    assert_eq!(
        observe(&exhaustion),
        vec![1],
        "32 rejected draws preserve state"
    );
    // A controlled counter stream makes the retry boundary observable: the
    // 32nd draw may succeed; a value first available on draw 33 must refuse.
    let boundary = Fixture::probe(
        "let g=rng::new(0,0);let snap=rng::new_snapshot();
        if rng::restore(g,snap)!=0 {return -1;}
        if rng::below(g,4294967265)!=31 || g.value!=32 {return -2;}
        if rng::restore(g,snap)!=0 {return -3;}
        if rng::below(g,4294967264)!=-429 || g.value!=0 {return -4;}
        observations.push(1);",
    );
    boundary.mutate(
        "return value * 6364136223846793005 + increment;",
        "return value + increment;",
    );
    boundary.mutate("return bits.as_i64();", "return value.as_i64();");
    assert_eq!(observe(&boundary), vec![1]);
    for label in ["Public", "Internal", "Secret"] {
        let fixture = Fixture::new();
        std::fs::write(
            fixture.root.join("src/tool.sigil"),
            format!(
            "module tool;use sigil::rng;fn sample(seed:u64 @{label})->i64 @{label} ! {{Alloc}} {{
            let g=rng::new(seed,0);return rng::next(g);}}
            pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return 0;}}"
        ),
        )
        .expect("label caller");
        fixture.lock();
        let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["check", "--package"])
            .arg(&fixture.root)
            .arg("--json")
            .output()
            .expect("check");
        if label == "Public" {
            assert!(output.status.success());
        } else {
            assert!(!output.status.success());
            let result: serde_json::Value = serde_json::from_slice(&output.stdout).expect("JSON");
            let codes = result["diagnostics"]
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

#[cfg(feature = "solver")]
#[test]
fn rng_proposal_fresh_workflow_replay_and_cpu_composition_execute() {
    let fixture = Fixture::new();
    let package = fixture.compile();
    let reference = json(&repo().join("library/tests/fixtures/autoresearch-cpu/torch-v1.json"));
    let wire = reference["cases"][0]["request_hex"].as_str().expect("wire");
    let mut request = b"APRP\x01\x00\x00\x00".to_vec();
    request.extend(42_u64.to_le_bytes());
    request.extend(54_u64.to_le_bytes());
    request.extend(wire.as_bytes().as_chunks::<2>().0.iter().map(|pair| {
        u8::from_str_radix(std::str::from_utf8(pair).expect("hex"), 16).expect("byte")
    }));
    let input = request
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>();
    let baseline = execute(&package, input.as_bytes()).expect("native proposal");
    for (cooperative, engine, memory) in [
        (1, 10_000_000, 16 * 1024 * 1024),
        (500_000, 1, 16 * 1024 * 1024),
        (500_000, 10_000_000, 1),
    ] {
        assert!(
            sigil_runtime::execute_ephemeral_with_budgets(
                &package.compilation.wasm_inner,
                input.as_bytes(),
                cooperative,
                engine,
                memory,
                &sigil_runtime::IoGrants::none()
            )
            .is_err()
        );
    }
    println!(
        "proposal sample: {} Wasm bytes, {} cooperative fuel",
        package.compilation.wasm_inner.len(),
        baseline.fuel_consumed
    );
    let allocating = Fixture::new();
    let path = allocating.root.join("src/tool.sigil");
    let source = std::fs::read_to_string(&path).expect("source");
    assert_eq!(source.matches("let before = alloc(0);").count(), 1);
    std::fs::write(
        path,
        source.replace(
            "let before = alloc(0);",
            "let before = alloc(0);let scratch=alloc(8);store8(scratch,1);",
        ),
    )
    .expect("live allocation fault");
    let failure = execute(&allocating.compile(), input.as_bytes());
    assert!(
        matches!(&failure,
        Err(sigil_runtime::ToolError::Trapped { message }) if message == "tool returned error (500)"),
        "{failure:?}"
    );
    let output = Command::new("python3")
        .arg("-W")
        .arg("error::ResourceWarning")
        .args([
            "-m",
            "unittest",
            "discover",
            "-s",
            "library/tests",
            "-p",
            "test_autoresearch_propose.py",
        ])
        .current_dir(repo())
        .env("SIGIL_INTEGRATION_CLI", env!("CARGO_BIN_EXE_sigil"))
        .output()
        .expect("proposal workflow tests");
    assert!(output.status.success(), "{output:?}");
}
