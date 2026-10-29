//! WHY THIS TEST EXISTS. Execute imported candidate bytecode, not canned losses.
//! Independent PyTorch answers, live mutants, fresh locks and refusal twins
//! distinguish numerical agreement from merely producing a plausible report.
#![cfg(unix)]

use sigil_compiler::package::{
    LocalPackageDependency, create_local_package_lock_with_dependencies,
};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
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
fn copy_package(source: &Path, destination: &Path) {
    std::fs::create_dir_all(destination).expect("owned directory");
    for entry in std::fs::read_dir(source).expect("package files") {
        let entry = entry.expect("entry");
        if [".sigil", "__pycache__", "sigil-package.lock.json"]
            .iter()
            .any(|name| entry.file_name() == *name)
        {
            continue;
        }
        let kind = entry.file_type().expect("type");
        if kind.is_dir() {
            copy_package(&entry.path(), &destination.join(entry.file_name()));
        } else {
            assert!(kind.is_file(), "fixture cannot follow symlinks");
            std::fs::copy(entry.path(), destination.join(entry.file_name())).expect("copy");
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
            let path = std::env::temp_dir().join(format!(
                "sigil-autoresearch-cpu-{}-{}",
                std::process::id(),
                SEQUENCE.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => break path,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create fixture: {e}"),
            }
        };
        let root = directory.join("consumer");
        let provider = directory.join("autodiff");
        copy_package(&repo().join("library/programs/autoresearch-cpu"), &root);
        copy_package(&repo().join("library/packages/autodiff"), &provider);
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
                package: "sigil/autodiff".into(),
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
        .expect("solver compilation")
    }
    #[cfg(feature = "solver")]
    fn mutate(&self, needle: &str, replacement: &str) {
        let path = self.root.join("src/tool.sigil");
        let original = std::fs::read_to_string(&path).expect("source");
        assert_eq!(
            original.matches(needle).count(),
            1,
            "unique live mutation site"
        );
        std::fs::write(path, original.replacen(needle, replacement, 1)).expect("owned mutant");
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}
fn cli(root: &Path, command: &str, extra: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_sigil"))
        .arg(command)
        .arg("--package")
        .arg(root)
        .args(extra)
        .arg("--json")
        .output()
        .expect("CLI")
}
fn envelope(output: &Output) -> serde_json::Value {
    serde_json::from_slice(&output.stdout).unwrap_or_else(|e| panic!("{e}: {output:?}"))
}

#[test]
fn autoresearch_cpu_metadata_and_fresh_graph_bind_actual_inputs() {
    let root = repo().join("library/programs/autoresearch-cpu");
    let manifest = json(&root.join("sigil-package.json"));
    for (field, file) in [
        ("api_card_hash", "api-card.json"),
        ("api_contract_hash", "API.md"),
        ("charter_hash", "README.md"),
        ("evidence_manifest_hash", "tool-inputs.json"),
    ] {
        assert_eq!(
            manifest["evidence"][field],
            hash(&std::fs::read(root.join(file)).expect("input"))
        );
    }
    let inventory = json(&root.join("tool-inputs.json"));
    assert_eq!(inventory["files"].as_object().expect("inventory").len(), 9);
    for (file, expected) in inventory["files"].as_object().expect("inventory") {
        let mut bytes = std::fs::read(root.join(file)).expect("input");
        assert_eq!(expected, &hash(&bytes));
        bytes.push(b'!');
        assert_ne!(expected, &hash(&bytes), "live inventory drift");
    }
    let fixture = Fixture::new();
    let lock = fixture.lock();
    let graph: serde_json::Value = serde_json::from_slice(&lock).expect("graph");
    assert_eq!(graph["nodes"].as_array().expect("nodes").len(), 2);
    let provider = graph["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .find(|node| node["package"] == "sigil/autodiff")
        .expect("provider");
    let cached = fixture
        .root
        .join(provider["source"]["locator"].as_str().expect("locator"));
    std::fs::write(cached.join("src/autodiff.sigil"), "module autodiff;\n").expect("drift");
    let refused = cli(&fixture.root, "check", &[]);
    assert!(!refused.status.success());
    assert_eq!(envelope(&refused)["data"]["code"], "E_HASH_MISMATCH");
    assert_eq!(
        std::fs::read(fixture.root.join("sigil-package.lock.json")).expect("lock"),
        lock
    );
}

#[cfg(feature = "solver")]
fn reference() -> serde_json::Value {
    json(&repo().join("library/tests/fixtures/autoresearch-cpu/torch-v1.json"))
}
#[cfg(feature = "solver")]
fn case(reference: &serde_json::Value, name: &str) -> serde_json::Value {
    reference["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .find(|case| case["name"] == name)
        .expect("required case")
        .clone()
}
#[cfg(feature = "solver")]
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
#[cfg(feature = "solver")]
fn unhex(input: &str) -> Vec<u8> {
    input
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|b| u8::from_str_radix(std::str::from_utf8(b).expect("hex"), 16).expect("byte"))
        .collect()
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
fn values(output: &[u8], request: &str) -> (i64, Vec<f64>) {
    let input = unhex(request);
    assert_eq!(output.len(), 144 + input.len());
    assert_eq!(&output[144..], input);
    let header: Vec<_> = output[..32]
        .as_chunks::<8>()
        .0
        .iter()
        .map(|chunk| i64::from_le_bytes(*chunk))
        .collect();
    assert_eq!(&header[..3], &[1, i64::from(input[5]), i64::from(input[6])]);
    let expected_nodes = 24 + i64::from(input[5]) * (7 + 2 * i64::from(input[6]));
    assert_eq!(header[3], expected_nodes);
    assert!(header[3] <= 768);
    (
        header[3],
        output[32..144]
            .as_chunks::<8>()
            .0
            .iter()
            .map(|chunk| f64::from_le_bytes(*chunk))
            .collect(),
    )
}
#[cfg(feature = "solver")]
fn expected(case: &serde_json::Value) -> Vec<f64> {
    serde_json::from_value(case["expected"].clone()).expect("finite oracle")
}
#[cfg(feature = "solver")]
fn agrees(actual: &[f64], expected: &[f64]) -> bool {
    actual.len() == expected.len()
        && actual.iter().zip(expected).all(|(a, b)| {
            a.is_finite() && b.is_finite() && (a - b).abs() <= 1e-10 + 1e-10 * b.abs()
        })
}
#[cfg(feature = "solver")]
fn refused(package: &sigil_compiler::package::PackageCompilation, input: &[u8], code: i64) {
    assert!(
        matches!(execute(package, input),
        Err(sigil_runtime::ToolError::Trapped {message}) if message == format!("tool returned error ({code})")),
        "malformed or numerically unsafe input must refuse: {input:?}"
    );
}

#[cfg(feature = "solver")]
#[test]
fn autoresearch_cpu_matches_pytorch_all_seeds_opcodes_and_boundaries() {
    let fixture = Fixture::new();
    let package = fixture.compile();
    let reference = reference();
    assert_eq!(reference["format"], "sigil-autoresearch-cpu-torch-v1");
    assert_eq!(reference["reference"]["torch"], "2.14.1");
    let cases = reference["cases"].as_array().expect("cases");
    assert_eq!(cases.len(), 41);
    let mut names = std::collections::BTreeSet::new();
    let mut max_fuel = 0;
    let mut fd_count = 0;
    for case in cases {
        let name = case["name"].as_str().expect("name");
        assert!(names.insert(name.to_owned()));
        let request = case["request_hex"].as_str().expect("wire");
        let result = execute(&package, request.as_bytes()).expect("bounded execution");
        let (_, actual) = values(&result.output, request);
        let expected = expected(case);
        assert!(
            agrees(&actual, &expected),
            "{name}: {actual:?} != {expected:?}"
        );
        let mut wrong = expected.clone();
        wrong[6] += wrong[6].abs() + 1.;
        assert!(
            !agrees(&actual, &wrong),
            "planted gradient error must be caught"
        );
        wrong[6] = f64::INFINITY;
        assert!(
            !agrees(&actual, &wrong),
            "infinity must not enlarge the tolerance"
        );
        if let Some(differences) = case["finite_difference"].as_array() {
            assert_eq!(differences.len(), 8);
            for (a, b) in actual[6..].iter().zip(differences) {
                let b = b.as_f64().expect("finite difference");
                assert!((a - b).abs() <= 2e-4 + 2e-6 * b.abs(), "{name}: {a} != {b}");
                fd_count += 1;
            }
        }
        assert_eq!(
            execute(&package, request.as_bytes())
                .expect("repeat")
                .output,
            result.output
        );
        max_fuel = max_fuel.max(result.fuel_consumed);
    }
    let mut required = std::collections::BTreeSet::new();
    for seed in ["sgd", "momentum", "step-decay"] {
        for steps in [0, 1, 2, 5, 10, 20] {
            required.insert(format!("{seed}-{steps}"));
        }
    }
    for op in 0..8 {
        required.insert(format!("opcode-{op}"));
    }
    for value in ["-1.0", "0.0", "0.25", "1.0", "2.0"] {
        required.insert(format!("step-{value}"));
    }
    for value in [
        "-4094.0", "-4095.0", "-4096.0", "4094.0", "4095.0", "4096.0",
    ] {
        required.insert(format!("clip-{value}"));
    }
    for name in [
        "stable-sgd-20",
        "stable-momentum-20",
        "all-eight-weights",
        "maximum-12x20",
    ] {
        required.insert(name.into());
    }
    assert_eq!(names, required, "mandatory cases cannot silently disappear");
    assert_eq!(fd_count, 120);
    eprintln!(
        "autoresearch CPU: 41 Torch states, 328 gradients, {fd_count} finite differences; maximum cooperative fuel {max_fuel}; Wasm {} bytes",
        package.compilation.wasm_inner.len()
    );
}

#[cfg(feature = "solver")]
#[test]
fn autoresearch_cpu_refuses_malformed_inputs_and_preserves_resource_limits() {
    let fixture = Fixture::new();
    let package = fixture.compile();
    let reference = reference();
    let valid = case(&reference, "momentum-20");
    let input = valid["request_hex"].as_str().expect("wire");
    assert!(
        execute(&package, input.as_bytes()).is_ok(),
        "positive control"
    );
    for (text, code) in [
        ("".into(), 422),
        (input[..151].into(), 422),
        (format!("{input}0"), 422),
        ("0".repeat(242), 413),
        (format!("z{}", &input[1..]), 422),
        (input.to_uppercase(), 422),
        (format!("{input}00"), 422),
    ] {
        refused(&package, text.as_bytes(), code);
    }
    for (at, byte, code) in [
        (0, 0, 422),
        (4, 2, 422),
        (5, 21, 413),
        (6, 0, 422),
        (6, 13, 413),
        (7, 2, 422),
        (72, 8, 422),
        (73, 0, 422),
        (73, 16, 422),
        (74, 16, 422),
        (75, 8, 422),
    ] {
        let mut bytes = unhex(input);
        bytes[at] = byte;
        refused(&package, hex(&bytes).as_bytes(), code);
    }
    for weight in [
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        4096.00001,
        -4096.00001,
    ] {
        let mut bytes = unhex(input);
        bytes[8..16].copy_from_slice(&weight.to_le_bytes());
        refused(&package, hex(&bytes).as_bytes(), 422);
    }
    let mut unary = unhex(
        case(&reference, "opcode-7")["request_hex"]
            .as_str()
            .expect("wire"),
    );
    unary[75] = 16;
    refused(&package, hex(&unary).as_bytes(), 422);
    // Finite primal zeros, but recurrent gains overflow the reverse sweep.
    let mut overflow = unhex(
        case(&reference, "maximum-12x20")["request_hex"]
            .as_str()
            .expect("wire"),
    );
    overflow[8..16].copy_from_slice(&4096f64.to_le_bytes());
    for index in 0..10 {
        overflow[72 + 4 * index..76 + 4 * index].copy_from_slice(&[4, 15, 15, 0]);
    }
    overflow[112..116].copy_from_slice(&[5, 15, 15, 1]);
    overflow[116..120].copy_from_slice(&[0, 14, 15, 1]);
    refused(&package, hex(&overflow).as_bytes(), 422);
    for (fuel, engine, memory) in [
        (1, 10_000_000, 16 * 1024 * 1024),
        (500_000, 1, 16 * 1024 * 1024),
        (500_000, 10_000_000, 1),
    ] {
        assert!(
            sigil_runtime::execute_ephemeral_with_budgets(
                &package.compilation.wasm_inner,
                input.as_bytes(),
                fuel,
                engine,
                memory,
                &sigil_runtime::IoGrants::none()
            )
            .is_err()
        );
    }
    assert_eq!(
        execute(&package, input.as_bytes())
            .expect("unchanged valid twin")
            .output,
        execute(&package, input.as_bytes()).expect("repeat").output
    );
}

#[cfg(feature = "solver")]
#[test]
fn autoresearch_cpu_live_mutants_change_observations_or_refuse() {
    let reference = reference();
    for (name, needle, replacement) in [
        (
            "momentum-20",
            "let backward = autodiff::backward(tape, loss);",
            "let backward = autodiff::backward(tape, weighted);",
        ),
        (
            "momentum-20",
            "registers.set(1, momentum.get(coordinate));",
            "registers.set(1, zero);",
        ),
        ("step-decay-20", "time / 20.0", "time / 10.0"),
        ("step-0.0", "cell.value <= low", "cell.value < low"),
        ("step-1.0", "cell.value >= high", "cell.value > high"),
        ("clip-4095.0", "cell.value >= high", "cell.value > high"),
    ] {
        let fixture = Fixture::new();
        fixture.mutate(needle, replacement);
        let package = fixture.compile();
        let case = case(&reference, name);
        let input = case["request_hex"].as_str().expect("wire");
        let output = execute(&package, input.as_bytes()).expect("live mutant executes");
        assert!(
            !agrees(&values(&output.output, input).1, &expected(&case)),
            "mutant {name} must be observable"
        );
    }
    for (needle, replacement, code) in [
        (
            "let before = alloc(0);",
            "let before = alloc(0); let leaked = alloc(8); store8(leaked, 1);",
            500,
        ),
        (
            "autodiff::new_tape(768, 0)",
            "autodiff::new_tape(32, 0)",
            413,
        ),
    ] {
        let fixture = Fixture::new();
        fixture.mutate(needle, replacement);
        let package = fixture.compile();
        let case = case(&reference, "momentum-20");
        refused(
            &package,
            case["request_hex"].as_str().expect("wire").as_bytes(),
            code,
        );
    }
}

#[cfg(feature = "solver")]
#[test]
fn autoresearch_cpu_fresh_wrapper_and_stale_certificate_refusal() {
    let fixture = Fixture::new();
    fixture.lock();
    let certificate = fixture.directory.join("cpu.cert.json");
    let cert = certificate.to_str().expect("path");
    let checked = cli(&fixture.root, "check", &["--cert", cert]);
    assert!(checked.status.success(), "{checked:?}");
    let checked = envelope(&checked);
    let certificate_data = &checked["data"]["certificate"];
    assert_eq!(
        certificate_data["ambient_stdlib"]["derived"]["host_imports"],
        serde_json::json!([])
    );
    let packages = certificate_data["packages"]
        .as_array()
        .expect("derived packages");
    assert_eq!(packages.len(), 2);
    for package in packages {
        assert_eq!(package["derived"]["host_imports"], serde_json::json!([]));
        assert_eq!(
            package["derived"]["grant_categories"],
            serde_json::json!([])
        );
    }
    assert!(
        cli(&fixture.root, "verify-cert", &["--cert", cert])
            .status
            .success()
    );
    let result = Command::new("python3")
        .arg(fixture.root.join("run.py"))
        .args(["--sigil", env!("CARGO_BIN_EXE_sigil"), "--package"])
        .arg(&fixture.root)
        .arg("--candidate")
        .arg(fixture.root.join("candidates/momentum.json"))
        .output()
        .expect("fresh wrapper");
    assert!(result.status.success(), "{result:?}");
    let displayed = envelope(&result);
    assert_eq!(displayed["inner_steps"], 20);
    let oracle = case(&reference(), "momentum-20");
    let input = oracle["request_hex"].as_str().expect("request");
    let run_with_certificate = || {
        cli(
            &fixture.root,
            "run",
            &["--input", input, "--fuel", "500000", "--cert", cert],
        )
    };
    assert!(
        run_with_certificate().status.success(),
        "certificate-backed positive control"
    );
    let expected = expected(&oracle);
    assert!(agrees(
        &[displayed["loss"].as_f64().expect("loss")],
        &expected[..1]
    ));
    let gradients: Vec<f64> =
        serde_json::from_value(displayed["gradient"].clone()).expect("gradients");
    assert!(agrees(&gradients, &expected[6..]));
    let before = std::fs::read(&certificate).expect("certificate");
    fixture.mutate("time / 20.0", "time / 10.0");
    assert!(
        !cli(&fixture.root, "verify-cert", &["--cert", cert])
            .status
            .success()
    );
    let stale = run_with_certificate();
    assert!(!stale.status.success());
    assert_eq!(envelope(&stale)["data"]["code"], "E_HASH_MISMATCH");
    std::fs::rename(
        fixture.root.join("sigil-package.lock.json"),
        fixture.directory.join("previous.lock.json"),
    )
    .expect("preserve lock");
    fixture.lock();
    assert!(
        !cli(&fixture.root, "verify-cert", &["--cert", cert])
            .status
            .success()
    );
    let stale = run_with_certificate();
    assert!(!stale.status.success());
    assert_eq!(envelope(&stale)["data"]["code"], "E_CERTIFICATE");
    assert_eq!(
        std::fs::read(certificate).expect("preserved certificate"),
        before
    );
}
