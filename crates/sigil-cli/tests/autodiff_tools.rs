//! WHY THIS TEST EXISTS. A decreasing regression loss does not establish reverse
//! mode. Execute real tapes against separately generated PyTorch answers and
//! exercise stale handles, fan-out, bounded failure and allocation observers.
//! Portable checks bind actual files; solver checks execute native SIGIL/Wasm.

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
    serde_json::from_slice(&std::fs::read(path).expect("read JSON artifact"))
        .expect("JSON artifact")
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
    std::fs::create_dir_all(destination.join("src")).expect("owned source directory");
    for entry in std::fs::read_dir(source).expect("package files") {
        let entry = entry.expect("entry");
        if entry.file_type().expect("type").is_file()
            && entry.file_name() != "sigil-package.lock.json"
        {
            std::fs::copy(entry.path(), destination.join(entry.file_name()))
                .expect("copy metadata");
        }
    }
    for entry in std::fs::read_dir(source.join("src")).expect("source files") {
        let entry = entry.expect("entry");
        assert!(entry.file_type().expect("type").is_file());
        std::fs::copy(
            entry.path(),
            destination.join("src").join(entry.file_name()),
        )
        .expect("copy source");
    }
}
struct Fixture {
    directory: PathBuf,
    root: PathBuf,
    provider: PathBuf,
}
impl Fixture {
    fn candidate() -> Self {
        let fixture = Self::new();
        copy_package(
            &repo().join("library/programs/candidate-fit"),
            &fixture.root,
        );
        fixture
    }
    fn new() -> Self {
        let directory = loop {
            let path = std::env::temp_dir().join(format!(
                "sigil-autodiff-{}-{}",
                std::process::id(),
                SEQUENCE.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => break path,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create owned fixture: {e}"),
            }
        };
        let root = directory.join("consumer");
        let provider = directory.join("autodiff");
        copy_package(&repo().join("library/programs/linear-regression"), &root);
        copy_package(&repo().join("library/packages/autodiff"), &provider);
        Self {
            directory,
            root,
            provider,
        }
    }
    #[cfg(feature = "solver")]
    fn repin(&self) {
        let derived: serde_json::Value = serde_json::from_slice(
            &sigil_compiler::package::derive_local_package_lock(&self.provider)
                .expect("actual provider identity"),
        )
        .expect("JSON");
        let mut manifest = json(&self.root.join("sigil-package.json"));
        let dependencies = manifest["dependencies"]
            .as_array_mut()
            .expect("dependencies");
        dependencies.retain(|dependency| dependency["package"] != "sigil/autodiff");
        dependencies.push(serde_json::json!({"package":"sigil/autodiff","requirement":"=0.1.0-public.1","source":"workspace","content_hash":derived["nodes"][0]["content_hash"],"features":[],"default_features":false,"optional":false}));
        dependencies.sort_by_key(|d| d["package"].as_str().expect("name").to_owned());
        std::fs::write(
            self.root.join("sigil-package.json"),
            serde_json::to_vec(&manifest).expect("encode"),
        )
        .expect("owned declaration");
    }
    fn lock(&self) -> Vec<u8> {
        create_local_package_lock_with_dependencies(
            &self.root,
            &[
                LocalPackageDependency {
                    package: "sigil/autodiff".into(),
                    path: self.provider.clone(),
                },
                LocalPackageDependency {
                    package: "sigil/numeric".into(),
                    path: repo().join("library/packages/numeric"),
                },
            ],
        )
        .expect("fresh locked graph")
    }
    #[cfg(feature = "solver")]
    fn probe(body: &str, integers: &[&str], numbers: &[&str]) -> Self {
        let fixture = Self::new();
        let mut source = format!(
            "module tool;use sigil::autodiff;use sigil::vec;pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{\n{body}\nlet ints:Vec<i64> = Vec::with_capacity({});let nums:Vec<f64> = Vec::with_capacity({});\n",
            integers.len(),
            numbers.len()
        );
        for value in integers {
            source.push_str(&format!("ints.push({value});\n"));
        }
        for value in numbers {
            source.push_str(&format!("nums.push({value});\n"));
        }
        let n = integers.len() * 8;
        let m = numbers.len() * 8;
        source.push_str(&format!("let blob=alloc({});let mut i=0;while i<{n} {{store8(blob+i,load8(ints.buf+i));i=i+1;}}i=0;while i<{m} {{store8(blob+{n}+i,load8(nums.buf+i));i=i+1;}}return blob*4294967296+{};}}",n+m,n+m));
        std::fs::write(fixture.root.join("src/tool.sigil"), source).expect("observation driver");
        fixture
    }
    #[cfg(feature = "solver")]
    fn compile(&self) -> sigil_compiler::package::PackageCompilation {
        self.lock();
        sigil_compiler::package::compile_local_package_with_context(
            &self.root,
            sigil_compiler::CompileOptions::default(),
            &sigil_compiler::CompilerContext::default(),
        )
        .expect("real solver graph")
    }
}

#[test]
fn candidate_fit_metadata_is_bound_and_cached_source_drift_refuses() {
    let root = repo().join("library/programs/candidate-fit");
    let manifest = json(&root.join("sigil-package.json"));
    for (field, file) in [
        ("api_card_hash", "api-card.json"),
        ("api_contract_hash", "API.md"),
        ("charter_hash", "README.md"),
        ("evidence_manifest_hash", "tool-inputs.json"),
    ] {
        assert_eq!(
            manifest["evidence"][field],
            hash(&std::fs::read(root.join(file)).expect("bound artifact"))
        );
    }
    for (file, expected) in json(&root.join("tool-inputs.json"))["files"]
        .as_object()
        .expect("inventory")
    {
        let mut bytes = std::fs::read(root.join(file)).expect("input");
        assert_eq!(expected, &hash(&bytes));
        bytes.push(b'!');
        assert_ne!(expected, &hash(&bytes), "inventory detects a changed input");
    }
    let fixture = Fixture::candidate();
    let lock = fixture.lock();
    let graph: serde_json::Value = serde_json::from_slice(&lock).expect("graph");
    assert_eq!(graph["nodes"].as_array().expect("nodes").len(), 3);
    let dependency = graph["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .find(|node| node["package"] == "sigil/autodiff")
        .expect("autodiff pin");
    let cached = fixture
        .root
        .join(dependency["source"]["locator"].as_str().expect("locator"));
    std::fs::write(cached.join("src/autodiff.sigil"), "module autodiff;\n")
        .expect("plant cached drift");
    let check = cli(&fixture.root, "check", &[]);
    assert!(!check.status.success());
    assert_eq!(envelope(&check)["data"]["code"], "E_HASH_MISMATCH");
    assert_eq!(
        std::fs::read(fixture.root.join("sigil-package.lock.json")).expect("retained lock"),
        lock
    );
}

#[cfg(feature = "solver")]
fn fit_execute(
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
fn fit_values(bytes: &[u8], candidate: i64, steps: i64) -> Vec<f64> {
    assert_eq!(bytes.len(), 304, "declared native report ABI");
    assert_eq!(
        i64::from_le_bytes(bytes[0..8].try_into().expect("candidate")),
        candidate
    );
    assert_eq!(
        i64::from_le_bytes(bytes[8..16].try_into().expect("steps")),
        steps
    );
    bytes[16..]
        .as_chunks::<8>()
        .0
        .iter()
        .map(|chunk| f64::from_le_bytes(*chunk))
        .collect()
}

#[cfg(feature = "solver")]
fn fit_agrees(actual: &[f64], expected: &[f64]) -> bool {
    actual.len() == expected.len()
        && actual.iter().zip(expected).all(|(a, b)| {
            a.is_finite() && b.is_finite() && (a - b).abs() <= 1e-12 + 1e-11 * b.abs()
        })
}

#[cfg(feature = "solver")]
#[test]
fn candidate_fit_matches_pytorch_gradients_updates_and_repeatability() {
    let fixture = Fixture::candidate();
    let package = fixture.compile();
    let reference = json(&repo().join("library/tests/fixtures/candidate-fit/torch-v1.json"));
    assert_eq!(reference["format"], "sigil-candidate-fit-torch-v1");
    assert_eq!(reference["reference"]["torch"], "2.14.1");
    let cases = reference["cases"].as_array().expect("oracle cases");
    assert_eq!(cases.len(), 14);
    let mut seen = std::collections::BTreeSet::new();
    let mut max_fuel = 0;
    for case in cases {
        let candidate = case["candidate"].as_i64().expect("candidate");
        let steps = case["steps"].as_i64().expect("steps");
        assert!(
            seen.insert((candidate, steps)),
            "reference states must be distinct"
        );
        let input = format!("{candidate}:{steps}");
        let result = fit_execute(&package, input.as_bytes()).expect("bounded candidate executes");
        let actual = fit_values(&result.output, candidate, steps);
        let expected: Vec<f64> = case["expected"]
            .as_array()
            .expect("answer")
            .iter()
            .map(|v| v.as_f64().expect("finite reference"))
            .collect();
        assert!(
            fit_agrees(&actual, &expected),
            "native candidate {input} disagrees with independently emitted PyTorch answers"
        );
        let mut wrong = expected.clone();
        wrong[28] += 0.25;
        assert!(
            !fit_agrees(&actual, &wrong),
            "comparator must detect a planted gradient error"
        );
        wrong[28] = f64::INFINITY;
        assert!(
            !fit_agrees(&actual, &wrong),
            "an infinite answer must not make the tolerance unbounded"
        );
        let differences = case["finite_difference_final"]
            .as_array()
            .expect("finite differences");
        assert_eq!(
            differences.len(),
            8,
            "every constant needs a finite difference"
        );
        for (gradient, difference) in actual[28..36].iter().zip(differences) {
            assert!(
                (gradient - difference.as_f64().expect("difference")).abs() <= 1e-8,
                "native gradients also match central differences away from train-data kinks"
            );
        }
        if steps == 0 {
            assert_eq!(&actual[4..12], &actual[12..20]);
        }
        if steps == 16 {
            assert!(actual[1] < actual[0] && actual[3] < actual[2]);
        }
        assert_eq!(
            fit_execute(&package, input.as_bytes())
                .expect("repeat")
                .output,
            result.output,
            "fresh execution repeats the exact native report"
        );
        max_fuel = max_fuel.max(result.fuel_consumed);
    }
    let required: std::collections::BTreeSet<_> = (0..2)
        .flat_map(|candidate| [0, 1, 2, 4, 8, 12, 16].map(|steps| (candidate, steps)))
        .collect();
    assert_eq!(
        seen, required,
        "both candidates require every declared update state"
    );
    assert_eq!(
        fit_execute(&package, b"").expect("default").output,
        fit_execute(&package, b"0:16").expect("explicit").output
    );
    eprintln!(
        "candidate fitting: 14 Torch states; maximum cooperative fuel {max_fuel}; Wasm {} bytes",
        package.compilation.wasm_inner.len()
    );
}

#[cfg(feature = "solver")]
#[test]
fn candidate_fit_refuses_bad_inputs_budgets_and_stale_certificates() {
    let fixture = Fixture::candidate();
    let package = fixture.compile();
    for (input, code) in [
        (b"2:0".as_slice(), 422),
        (b"0:17", 422),
        (b"0:03", 422),
        (b"0:-1", 422),
        (b"0:1\n", 422),
        (b"0:1x", 422),
        (b"0", 422),
        (b":0", 422),
        (b"0:a", 422),
        (b"\xff:0", 422),
        (b"0:100", 413),
    ] {
        assert!(
            matches!(fit_execute(&package,input),Err(sigil_runtime::ToolError::Trapped{message}) if message==format!("tool returned error ({code})")),
            "bad request refuses: {input:?}"
        );
    }
    for (engine, memory) in [(1, 16 * 1024 * 1024), (10_000_000, 1)] {
        assert!(
            sigil_runtime::execute_ephemeral_with_budgets(
                &package.compilation.wasm_inner,
                b"0:1",
                500_000,
                engine,
                memory,
                &sigil_runtime::IoGrants::none()
            )
            .is_err(),
            "lower engine/memory limits still refuse"
        );
    }
    let low = cli(&fixture.root, "run", &["--input", "1:16", "--fuel", "1"]);
    assert!(!low.status.success());
    assert_eq!(
        envelope(&low)["diagnostics"][0]["code"],
        concat!("R", "801")
    );
    let certificate = fixture.directory.join("candidate.cert.json");
    let cert = certificate.to_str().expect("certificate path");
    assert!(
        cli(&fixture.root, "check", &["--cert", cert])
            .status
            .success()
    );
    assert!(
        cli(&fixture.root, "verify-cert", &["--cert", cert])
            .status
            .success()
    );
    let full = cli(
        &fixture.root,
        "run",
        &["--input", "1:16", "--fuel", "500000", "--cert", cert],
    );
    assert!(
        full.status.success(),
        "{}",
        String::from_utf8_lossy(&full.stdout)
    );
    let viewer = Command::new("python3")
        .arg(repo().join("library/programs/candidate-fit/run.py"))
        .args(["--sigil", env!("CARGO_BIN_EXE_sigil"), "--package"])
        .arg(&fixture.root)
        .args(["--candidate", "1", "--steps", "16"])
        .output()
        .expect("native viewer");
    assert!(
        viewer.status.success(),
        "{}",
        String::from_utf8_lossy(&viewer.stderr)
    );
    let displayed: serde_json::Value =
        serde_json::from_slice(&viewer.stdout).expect("displayed native report");
    assert_eq!(displayed["candidate"], 1);
    assert_eq!(displayed["steps"], 16);
    assert_eq!(
        displayed["constants"].as_array().expect("constants").len(),
        8
    );
    assert!(displayed["final_loss"].as_f64().expect("loss") < 0.008);
    let before = std::fs::read(&certificate).expect("certificate bytes");
    let source = fixture.root.join("src/tool.sigil");
    let text = std::fs::read_to_string(&source).expect("source");
    let changed = text.replace("let mut steps = 16;", "let mut steps = 15;");
    assert_ne!(text, changed);
    std::fs::write(source, changed).expect("plant changed source");
    let stale = cli(
        &fixture.root,
        "run",
        &["--input", "1:16", "--fuel", "500000", "--cert", cert],
    );
    assert!(!stale.status.success());
    assert_eq!(envelope(&stale)["data"]["code"], "E_HASH_MISMATCH");
    std::fs::rename(
        fixture.root.join("sigil-package.lock.json"),
        fixture.directory.join("previous.lock.json"),
    )
    .expect("preserve previous graph");
    fixture.lock();
    let stale = cli(
        &fixture.root,
        "run",
        &["--input", "1:16", "--fuel", "500000", "--cert", cert],
    );
    assert!(!stale.status.success());
    assert_eq!(envelope(&stale)["data"]["code"], "E_CERTIFICATE");
    assert_eq!(
        std::fs::read(certificate).expect("retained certificate"),
        before
    );
}

#[cfg(feature = "solver")]
#[test]
fn candidate_fit_live_mutants_and_validation_isolation_are_observable() {
    let baseline = Fixture::candidate();
    let package = baseline.compile();
    let normal = fit_execute(&package, b"0:8").expect("clean control");
    let expected = fit_values(&normal.output, 0, 8);
    for (old, new) in [
        (
            "numeric::sgd_step(weights, gradient, 0.1)",
            "numeric::sgd_step(weights, gradient, 0.0)",
        ),
        (
            "let left_relu = autodiff::relu(tape, left_shift);",
            "let left_relu = left_shift;",
        ),
        (
            "let update = numeric::sgd_step(weights, gradient, 0.1);",
            "let severed = numeric::set(gradient, 2, 0, 0.0); if severed < 0 { return severed; } else {} let update = numeric::sgd_step(weights, gradient, 0.1);",
        ),
    ] {
        let fixture = Fixture::candidate();
        let path = fixture.root.join("src/tool.sigil");
        let text = std::fs::read_to_string(&path).expect("source");
        let changed = text.replace(old, new);
        assert_ne!(text, changed, "mutation must plant");
        std::fs::write(path, changed).expect("live mutant");
        let result = fit_execute(&fixture.compile(), b"0:8")
            .expect("mutant executes, not a compile-failure kill");
        assert!(
            !fit_agrees(&fit_values(&result.output, 0, 8), &expected),
            "numerical observer must detect executed mutant: {old}"
        );
    }
    for (old, new, code) in [
        (
            "while step < steps {",
            "while step < steps { let growth = alloc(8);",
            500,
        ),
        (
            "autodiff::new_tape(256, 8)",
            "autodiff::new_tape(8, 8)",
            413,
        ),
    ] {
        let fixture = Fixture::candidate();
        let path = fixture.root.join("src/tool.sigil");
        let text = std::fs::read_to_string(&path).expect("source");
        let changed = text.replace(old, new);
        assert_ne!(text, changed);
        std::fs::write(path, changed).expect("bounded failure control");
        assert!(
            matches!(fit_execute(&fixture.compile(),b"0:1"),Err(sigil_runtime::ToolError::Trapped{message}) if message==format!("tool returned error ({code})"))
        );
    }
    let held = Fixture::candidate();
    let path = held.root.join("src/tool.sigil");
    let text = std::fs::read_to_string(&path).expect("source");
    let changed = text.replace(
        "validation_y.push(0.0 - 0.4575000000000001)",
        "validation_y.push(999.0)",
    );
    assert_ne!(text, changed);
    std::fs::write(path, changed).expect("change validation target only");
    let held_package = held.compile();
    for candidate in [0, 1] {
        let input = format!("{candidate}:8");
        let clean = fit_values(
            &fit_execute(&package, input.as_bytes())
                .expect("control")
                .output,
            candidate,
            8,
        );
        let changed = fit_values(
            &fit_execute(&held_package, input.as_bytes())
                .expect("validation change")
                .output,
            candidate,
            8,
        );
        assert_eq!(
            &clean[..2],
            &changed[..2],
            "validation target cannot affect training losses"
        );
        assert_eq!(
            &clean[4..],
            &changed[4..],
            "validation target cannot affect constants or gradients"
        );
        assert_ne!(clean[2], changed[2]);
        assert_ne!(clean[3], changed[3]);
    }
    // The isolation observer must also detect a real leak, not merely agree
    // on two clean executions. Plant the validation objective as training loss.
    let mut leaked_reports = Vec::new();
    for changed_target in [false, true] {
        let leak = Fixture::candidate();
        let path = leak.root.join("src/tool.sigil");
        let text = std::fs::read_to_string(&path).expect("source");
        let mut changed = text.replace(
            "let loss = objective(tape, candidate, weights, scalar, p, train_x, train_y, train_terms, 0.125);",
            "let loss = objective(tape, candidate, weights, scalar, p, validation_x, validation_y, validation_terms, 0.25);",
        );
        assert_ne!(text, changed, "validation leakage must actually plant");
        if changed_target {
            let next = changed.replace(
                "validation_y.push(0.0 - 0.4575000000000001)",
                "validation_y.push(999.0)",
            );
            assert_ne!(changed, next);
            changed = next;
        }
        std::fs::write(path, changed).expect("plant executable validation leakage");
        let result = fit_execute(&leak.compile(), b"0:1").expect("leaking program executes");
        leaked_reports.push(fit_values(&result.output, 0, 1));
    }
    assert_ne!(
        &leaked_reports[0][12..20],
        &leaked_reports[1][12..20],
        "the isolation observer must detect the planted target-dependent update"
    );
}
impl Drop for Fixture {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.directory).expect("remove only creator-owned fixture");
    }
}
fn cli(root: &Path, verb: &str, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args([verb, "--package"])
        .arg(root)
        .args(args)
        .arg("--json")
        .output()
        .expect("actual package CLI")
}
fn envelope(output: &Output) -> serde_json::Value {
    serde_json::from_slice(&output.stdout)
        .unwrap_or_else(|e| panic!("JSON {e}: {}", String::from_utf8_lossy(&output.stdout)))
}
#[cfg(feature = "solver")]
fn execute(
    package: &sigil_compiler::package::PackageCompilation,
    input: &[u8],
) -> Result<sigil_runtime::ToolResult, sigil_runtime::ToolError> {
    sigil_runtime::execute_ephemeral_with_budgets(
        &package.compilation.wasm_inner,
        input,
        250_000,
        10_000_000,
        16 * 1024 * 1024,
        &sigil_runtime::IoGrants::none(),
    )
}
#[cfg(feature = "solver")]
fn observe(fixture: &Fixture, count: usize) -> (Vec<i64>, Vec<f64>, u64) {
    let result = execute(&fixture.compile(), b"").expect("native probe executes");
    let bytes = &result.output;
    assert!(bytes.len() >= count * 8 && bytes.len().is_multiple_of(8));
    let integers = bytes[..count * 8]
        .as_chunks::<8>()
        .0
        .iter()
        .map(|p| i64::from_le_bytes(*p))
        .collect();
    let numbers = bytes[count * 8..]
        .as_chunks::<8>()
        .0
        .iter()
        .map(|p| f64::from_le_bytes(*p))
        .collect();
    (integers, numbers, result.fuel_consumed)
}
#[test]
fn autodiff_metadata_and_changed_cached_source_are_bound() {
    let root = repo().join("library/packages/autodiff");
    let manifest = json(&root.join("sigil-package.json"));
    for (field, file) in [
        ("api_card_hash", "api-card.json"),
        ("api_contract_hash", "API.md"),
        ("charter_hash", "README.md"),
        ("evidence_manifest_hash", "inputs.json"),
    ] {
        assert_eq!(
            manifest["evidence"][field],
            hash(&std::fs::read(root.join(file)).expect("actual file"))
        );
    }
    for (file, expected) in json(&root.join("inputs.json"))["files"]
        .as_object()
        .expect("inventory")
    {
        let mut bytes = std::fs::read(root.join(file)).expect("input");
        assert_eq!(expected, &hash(&bytes));
        bytes.push(b'!');
        assert_ne!(expected, &hash(&bytes));
    }
    let fixture = Fixture::new();
    let lock = fixture.lock();
    let graph: serde_json::Value = serde_json::from_slice(&lock).expect("JSON");
    assert_eq!(graph["nodes"].as_array().expect("nodes").len(), 3);
    let node = graph["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .find(|n| n["package"] == "sigil/autodiff")
        .expect("autodiff");
    std::fs::write(
        fixture
            .root
            .join(node["source"]["locator"].as_str().expect("locator"))
            .join("src/autodiff.sigil"),
        "module autodiff;\n",
    )
    .expect("plant cache drift");
    let output = cli(&fixture.root, "check", &[]);
    assert!(!output.status.success());
    assert_eq!(envelope(&output)["data"]["code"], "E_HASH_MISMATCH");
    assert_eq!(
        std::fs::read(fixture.root.join("sigil-package.lock.json")).expect("retained lock"),
        lock
    );
}
#[cfg(feature = "solver")]
#[test]
fn autodiff_shared_operands_repeat_backward_and_reset_are_observable() {
    // Refill the same slot after reset: an empty graph alone could reject an
    // old handle on its index bound without ever checking the reset epoch.
    let fixture = Fixture::probe(
        "let tape=autodiff::new_tape(8,4);let cell=autodiff::new_cell();let before=alloc(0);let x=autodiff::variable(tape,3.0);let y=autodiff::mul(tape,x,x);let first=autodiff::backward(tape,y);let query=autodiff::gradient_into(tape,x,cell);let one=cell.value;let second=autodiff::backward(tape,y);let again=autodiff::gradient_into(tape,x,cell);let two=cell.value;let sweep=tape.last_sweep;let cleared=autodiff::reset(tape);let replacement=autodiff::variable(tape,99.0);if replacement<0 {return replacement;} else {}let stale=autodiff::value_into(tape,x,cell);let delta=alloc(0)-before;",
        &[
            "first", "query", "second", "again", "sweep", "cleared", "stale", "delta",
        ],
        &["one", "two", "cell.value"],
    );
    let (integers, values, fuel) = observe(&fixture, 8);
    assert_eq!(integers, vec![0, 0, 0, 0, 2, 0, -400, 0]);
    assert_eq!(values, vec![6.0, 6.0, 6.0]);
    eprintln!("autodiff shared/reset probe fuel {fuel}");
}

#[cfg(feature = "solver")]
fn close(actual: &[f64], expected: &[f64]) {
    assert_eq!(actual.len(), expected.len());
    for (a, b) in actual.iter().zip(expected) {
        assert!(
            a.is_finite() && (a - b).abs() <= 1e-12 + 1e-11 * b.abs(),
            "native {a:.17}, reference {b:.17}"
        );
    }
}
#[cfg(feature = "solver")]
fn literal(value: f64) -> String {
    if value.is_sign_negative() {
        format!("(0.0 - {:.17})", value.abs())
    } else {
        format!("{value:.17}")
    }
}
#[cfg(feature = "solver")]
fn reference() -> serde_json::Value {
    serde_json::from_str(include_str!(
        "../../../library/tests/fixtures/autodiff/torch-v1.json"
    ))
    .expect("executed PyTorch answers")
}
#[cfg(feature = "solver")]
fn graph_probe(case: &serde_json::Value, planted: &str) -> Fixture {
    let nodes = case["nodes"].as_array().expect("nodes");
    let edge_count: usize = nodes
        .iter()
        .filter(|n| n["op"] == "sum")
        .map(|n| n["terms"].as_array().expect("terms").len())
        .sum();
    let variables: Vec<usize> = nodes
        .iter()
        .enumerate()
        .filter_map(|(i, n)| (n["op"] == "variable").then_some(i))
        .collect();
    let mut body = format!(
        "let skew=alloc(1);let tape=autodiff::new_tape({},{});let cell=autodiff::new_cell();let answers:Vec<f64> = Vec::with_capacity({});let mut fill=0;while fill<{} {{answers.push(0.0);fill=fill+1;}}\n",
        nodes.len(),
        edge_count,
        variables.len() + 1,
        variables.len() + 1
    );
    for (i, node) in nodes.iter().enumerate().filter(|(_, n)| n["op"] == "sum") {
        let count = node["terms"].as_array().expect("terms").len();
        body.push_str(&format!("let terms{i}:Vec<i64> = Vec::with_capacity({count});fill=0;while fill<{count} {{terms{i}.push(0);fill=fill+1;}}\n"));
    }
    body.push_str("let before=alloc(0);\n");
    for (i, node) in nodes.iter().enumerate() {
        let op = node["op"].as_str().expect("op");
        let call = match op {
            "variable" | "constant" => format!(
                "autodiff::{op}(tape,{})",
                literal(node["value"].as_f64().expect("scalar"))
            ),
            "relu" => format!("autodiff::relu(tape,n{})", node["a"]),
            "select" => format!(
                "autodiff::select(tape,{},n{},n{})",
                node["condition"], node["a"], node["b"]
            ),
            "sum" => {
                for (j, parent) in node["terms"].as_array().expect("terms").iter().enumerate() {
                    body.push_str(&format!("terms{i}.set({j},n{parent});\n"));
                }
                format!("autodiff::sum(tape,terms{i})")
            }
            _ => format!("autodiff::{op}(tape,n{},n{})", node["a"], node["b"]),
        };
        body.push_str(&format!(
            "let n{i}={call};if n{i}<0 {{return n{i};}} else {{}}\n"
        ));
    }
    let output = case["output"].as_u64().expect("root");
    body.push_str(&format!("{planted}\nlet backward=autodiff::backward(tape,n{output});if backward<0 {{return backward;}} else {{}}let read=autodiff::value_into(tape,n{output},cell);if read<0 {{return read;}} else {{}}answers.set(0,cell.value);\n"));
    for (i, variable) in variables.iter().enumerate() {
        body.push_str(&format!("let g{i}=autodiff::gradient_into(tape,n{variable},cell);if g{i}<0 {{return g{i};}} else {{}}answers.set({},cell.value);\n",i+1));
    }
    body.push_str("let delta=alloc(0)-before;\n");
    let numbers: Vec<String> = (0..=variables.len())
        .map(|i| format!("answers.get({i})"))
        .collect();
    Fixture::probe(
        &body,
        &["backward", "delta", "tape.last_sweep", "tape.used"],
        &numbers.iter().map(String::as_str).collect::<Vec<_>>(),
    )
}
#[cfg(feature = "solver")]
#[test]
fn autodiff_graph_gradients_match_pytorch_without_allocation() {
    let reference = reference();
    assert_eq!(reference["reference"]["torch"], "2.14.1");
    assert_eq!(reference["reference"]["dtype"], "float64");
    assert_eq!(reference["reference"]["device"], "cpu");
    let graphs = reference["graphs"].as_array().expect("graphs");
    assert!(graphs.len() >= 64, "reference deletion floor");
    let mut max_fuel = 0;
    for case in graphs {
        let fixture = graph_probe(case, "");
        let (state, actual, fuel) = observe(&fixture, 4);
        let count = case["nodes"].as_array().expect("nodes").len() as i64;
        assert_eq!(state, vec![0, 0, count, count], "{}", case["name"]);
        close(
            &actual,
            &serde_json::from_value::<Vec<f64>>(case["expected"].clone()).expect("Torch values"),
        );
        max_fuel = max_fuel.max(fuel);
    }
    let allocating = graph_probe(&graphs[0], "let scratch=alloc(8);");
    assert_eq!(
        observe(&allocating, 4).0[1],
        8,
        "positive allocation control"
    );
    eprintln!(
        "autodiff: {} Torch graph comparisons; whole-probe maximum fuel {max_fuel}",
        graphs.len()
    );
    assert!(max_fuel <= 16_000, "fixed graph corpus fuel ceiling");
    let polynomial = graphs
        .iter()
        .find(|case| case["name"] == "shared-polynomial")
        .expect("smooth finite-difference case");
    let actual = observe(&graph_probe(polynomial, ""), 4).1;
    for variable in 0..2 {
        let mut shifted = polynomial.clone();
        let value = shifted["nodes"][variable]["value"].as_f64().expect("input");
        shifted["nodes"][variable]["value"] = (value - 0.0001).into();
        let low = observe(&graph_probe(&shifted, ""), 4).1[0];
        shifted["nodes"][variable]["value"] = (value + 0.0001).into();
        let high = observe(&graph_probe(&shifted, ""), 4).1[0];
        assert!(
            ((high - low) / 0.0002 - actual[variable + 1]).abs() < 1e-7,
            "native finite difference agrees with reverse mode away from branch boundaries"
        );
    }
}
#[cfg(feature = "solver")]
#[test]
fn autodiff_linear_regression_matches_pytorch_with_the_real_package_budgets() {
    let fixture = Fixture::new();
    let package = fixture.compile();
    let baseline: serde_json::Value = serde_json::from_str(include_str!(
        "../../../library/tests/fixtures/numeric/torch-v1.json"
    ))
    .expect("original Torch training answers");
    let mut max_fuel = 0;
    for case in baseline["training"].as_array().expect("training states") {
        let result = execute(&package, case["epochs"].to_string().as_bytes())
            .expect("native tape training under unchanged engine/memory cap");
        let actual: Vec<f64> = result
            .output
            .as_chunks::<8>()
            .0
            .iter()
            .map(|part| f64::from_le_bytes(*part))
            .collect();
        close(
            &actual,
            &serde_json::from_value::<Vec<f64>>(case["expected"].clone()).expect("Torch training"),
        );
        max_fuel = max_fuel.max(result.fuel_consumed);
    }
    assert!(max_fuel < 240_000, "measured bounded training fuel ceiling");
    assert_eq!(
        execute(&package, b"").expect("default workload").output,
        execute(&package, b"100").expect("explicit default").output
    );
    for input in [
        b"-1".as_slice(),
        b"201",
        b"abc",
        b"1.0",
        b"1000",
        b"\xff",
        b" ",
        b"1\n",
    ] {
        assert!(
            matches!(
                execute(&package, input),
                Err(sigil_runtime::ToolError::Trapped { .. })
            ),
            "invalid epoch input refuses {input:?}"
        );
    }
    let certificate = fixture.directory.join("tape.cert.json");
    let cert = certificate.to_str().expect("path");
    assert!(
        cli(&fixture.root, "check", &["--cert", cert])
            .status
            .success()
    );
    assert!(
        cli(&fixture.root, "verify-cert", &["--cert", cert])
            .status
            .success()
    );
    let low = cli(&fixture.root, "run", &["--input", "100", "--fuel", "1"]);
    assert!(!low.status.success());
    assert_eq!(
        envelope(&low)["diagnostics"][0]["code"],
        concat!("R", "801")
    );
    let full = cli(
        &fixture.root,
        "run",
        &["--input", "200", "--fuel", "250000"],
    );
    assert!(
        full.status.success(),
        "{}",
        String::from_utf8_lossy(&full.stdout)
    );
    let viewer = Command::new("python3")
        .arg(repo().join("library/programs/linear-regression/run.py"))
        .args(["--sigil", env!("CARGO_BIN_EXE_sigil"), "--package"])
        .arg(&fixture.root)
        .args(["--steps", "100"])
        .output()
        .expect("stdlib-only viewer");
    assert!(
        viewer.status.success(),
        "{}",
        String::from_utf8_lossy(&viewer.stderr)
    );
    let display: serde_json::Value = serde_json::from_slice(&viewer.stdout).expect("display JSON");
    assert!(display["final_loss"].as_f64().expect("loss") < 0.00001);
    let source = fixture.root.join("src/tool.sigil");
    let original = std::fs::read_to_string(&source).expect("source");
    let changed = original.replace("let mut epochs = 100;", "let mut epochs = 99;");
    assert_ne!(original, changed);
    std::fs::write(&source, changed).expect("root source edit");
    let stale = cli(
        &fixture.root,
        "run",
        &["--input", "100", "--cert", cert, "--fuel", "250000"],
    );
    assert!(!stale.status.success());
    assert_eq!(envelope(&stale)["data"]["code"], "E_HASH_MISMATCH");
    let old_certificate = std::fs::read(&certificate).expect("certificate");
    std::fs::rename(
        fixture.root.join("sigil-package.lock.json"),
        fixture.directory.join("before-source-edit.lock.json"),
    )
    .expect("preserve previous lock");
    fixture.lock();
    let stale = cli(
        &fixture.root,
        "run",
        &["--input", "100", "--cert", cert, "--fuel", "250000"],
    );
    assert!(!stale.status.success());
    assert_eq!(envelope(&stale)["data"]["code"], "E_CERTIFICATE");
    assert_eq!(
        std::fs::read(&certificate).expect("retained cert"),
        old_certificate
    );
    let allocating = Fixture::new();
    let source = allocating.root.join("src/tool.sigil");
    let text = std::fs::read_to_string(&source).expect("source");
    let changed = text.replace(
        "while step < epochs {",
        "while step < epochs { let scratch=alloc(8);",
    );
    assert_ne!(text, changed);
    std::fs::write(source, changed).expect("plant real allocation");
    assert!(
        matches!(execute(&allocating.compile(),b"1"),Err(sigil_runtime::ToolError::Trapped{message}) if message=="tool returned error (500)"),
        "actual epoch allocation trips the unchanged heap fence"
    );
    eprintln!(
        "autodiff training: six Torch states; maximum SIGIL fuel {max_fuel}; Wasm {} bytes",
        package.compilation.wasm_inner.len()
    );
}

#[cfg(feature = "solver")]
#[test]
fn autodiff_refusals_preserve_graph_gradients_and_query_cells() {
    let setup = "let tape=autodiff::new_tape(8,4);let cell=autodiff::new_cell();cell.value=77.0;let x=autodiff::variable(tape,3.0);let y=autodiff::variable(tape,2.0);let z=autodiff::mul(tape,x,x);let good=autodiff::backward(tape,z);if good<0 {return good;} else {}let ids:Vec<i64> = Vec::with_capacity(2);ids.push(x);ids.push(y);let updates:Vec<f64> = Vec::with_capacity(2);updates.push(1.0);updates.push(2.0);";
    let mut cases = vec![
        ("", "autodiff::value_into(tape,0,cell)", -400),
        ("", "autodiff::value_into(tape,z+1,cell)", -400),
        ("", "autodiff::gradient_into(tape,z,cell)", -400),
        ("", "autodiff::backward(tape,-1)", -400),
        (
            "let other=autodiff::new_tape(8,4);let foreign=autodiff::variable(other,3.0);",
            "autodiff::add(tape,x,foreign)",
            -400,
        ),
        (
            "let cleared=autodiff::reset(tape);",
            "autodiff::value_into(tape,x,cell)",
            -400,
        ),
        (
            "let newer=autodiff::constant(tape,1.0);",
            "autodiff::gradient_into(tape,x,cell)",
            -400,
        ),
        ("", "autodiff::variable(tape,0.0/0.0)", -422),
        ("", "autodiff::constant(tape,1.0/0.0)", -422),
        (
            "let mut j=0;while j<5 {let n=autodiff::constant(tape,1.0);j=j+1;}",
            "autodiff::add(tape,x,y)",
            -413,
        ),
        ("ids.set(1,-1);", "autodiff::sum(tape,ids)", -400),
        ("tape.sum_used=3;", "autodiff::sum(tape,ids)", -413),
        ("tape.values.slots=7;", "autodiff::backward(tape,z)", -400),
        ("ids.buf=-1;", "autodiff::sum(tape,ids)", -400),
        ("ids.buf=2147483647;", "autodiff::sum(tape,ids)", -400),
        ("tape.left.buf=-1;", "autodiff::backward(tape,z)", -400),
        ("tape.capacity=4097;", "autodiff::constant(tape,1.0)", -400),
        (
            "tape.operations.set(2,8);",
            "autodiff::backward(tape,z)",
            -400,
        ),
        ("tape.left.set(2,2);", "autodiff::backward(tape,z)", -400),
        (
            "tape.right.set(2,99);",
            "autodiff::replay(tape,ids,updates)",
            -400,
        ),
        ("tape.epoch=1048574;", "autodiff::reset(tape)", -413),
        ("ids.set(1,x);", "autodiff::replay(tape,ids,updates)", -400),
        ("ids.set(1,z);", "autodiff::replay(tape,ids,updates)", -400),
        (
            "updates.count=1;",
            "autodiff::replay(tape,ids,updates)",
            -400,
        ),
        (
            "updates.set(1,1.0/0.0);",
            "autodiff::replay(tape,ids,updates)",
            -422,
        ),
        ("", "autodiff::new_tape(0,0).error", -400),
        ("", "autodiff::new_tape(-1,0).error", -400),
        ("", "autodiff::new_tape(1,-1).error", -400),
        ("", "autodiff::new_tape(4097,0).error", -413),
        ("", "autodiff::new_tape(1,4097).error", -413),
    ];
    let hundred = "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0";
    let overflow =
        format!("let big={hundred}*{hundred}*{hundred};let huge=autodiff::constant(tape,big);");
    cases.push((&overflow, "autodiff::mul(tape,huge,huge)", -422));
    for (extra, call, expected) in &cases {
        let body = format!(
            "{setup}{extra}let old_used=tape.used;let old_edges=tape.sum_used;let old_epoch=tape.epoch;let old_root=tape.last_root;let mut old_ready=0;if tape.ready {{old_ready=1;}} else {{}}let before=alloc(0);let code={call};let delta=alloc(0)-before;let mut ready=0;if tape.ready {{ready=1;}} else {{}}"
        );
        let fixture = Fixture::probe(
            &body,
            &[
                "code",
                "delta",
                "old_used",
                "tape.used",
                "old_edges",
                "tape.sum_used",
                "old_epoch",
                "tape.epoch",
                "old_root",
                "tape.last_root",
                "old_ready",
                "ready",
            ],
            &[
                "tape.values.get(0)",
                "tape.values.get(1)",
                "tape.values.get(2)",
                "tape.gradients.get(0)",
                "tape.gradients.get(1)",
                "tape.gradients.get(2)",
                "cell.value",
            ],
        );
        let (state, values, _) = observe(&fixture, 12);
        assert_eq!(state[0], *expected, "{call}");
        if !call.contains("new_tape") {
            assert_eq!(state[1], 0, "{call}");
        }
        for pair in state[2..].as_chunks::<2>().0 {
            assert_eq!(
                pair[0], pair[1],
                "returned error preserves published metadata: {call}"
            );
        }
        assert_eq!(values, vec![3.0, 2.0, 9.0, 6.0, 0.0, 1.0, 77.0], "{call}");
    }
    let maximum = Fixture::probe(
        "let tape=autodiff::new_tape(4096,4096);let cell=autodiff::new_cell();let before=alloc(0);let x=autodiff::variable(tape,2.0);let code=autodiff::value_into(tape,x,cell);let delta=alloc(0)-before;",
        &["tape.error", "code", "delta"],
        &["cell.value"],
    );
    let (state, values, _) = observe(&maximum, 3);
    assert_eq!(state, vec![0, 0, 0]);
    assert_eq!(values, vec![2.0]);
    eprintln!(
        "autodiff: {} refusal cases and exact maximum constructor",
        cases.len()
    );
}

#[cfg(feature = "solver")]
#[test]
fn autodiff_replay_and_backward_overflow_preserve_the_previous_publication() {
    let reference = reference();
    let graphs = reference["graphs"].as_array().expect("graphs");
    for (name, condition, updated) in [
        ("relu-3.0", None, 3.0),
        ("relu-0.0", None, 0.0),
        ("select-True", Some(true), 2.0),
        ("select-False", Some(false), 2.0),
    ] {
        let make_root=condition.map_or_else(||"let root=autodiff::relu(tape,x);".to_owned(),|flag|format!("let product=autodiff::mul(tape,x,y);let root=autodiff::select(tape,{flag},x,product);"));
        let mut body = format!(
            "let tape=autodiff::new_tape(8,0);let cell=autodiff::new_cell();let x=autodiff::variable(tape,0.0-2.0);let y=autodiff::variable(tape,1.0);{make_root}let ids:Vec<i64> = Vec::with_capacity(2);ids.push(x);ids.push(y);let updates:Vec<f64> = Vec::with_capacity(2);updates.push({});updates.push(0.0-3.0);let before=alloc(0);let replay=autodiff::replay(tape,ids,updates);let backward=autodiff::backward(tape,root);let read=autodiff::value_into(tape,root,cell);let value=cell.value;let gx=autodiff::gradient_into(tape,x,cell);let dx=cell.value;",
            literal(updated)
        );
        let mut numbers = vec!["value", "dx"];
        if condition.is_some() {
            body.push_str("let gy=autodiff::gradient_into(tape,y,cell);let dy=cell.value;");
            numbers.push("dy");
        }
        body.push_str("let delta=alloc(0)-before;");
        let fixture = Fixture::probe(
            &body,
            &["replay", "backward", "read", "gx", "delta"],
            &numbers,
        );
        let (state, values, _) = observe(&fixture, 5);
        assert_eq!(state, vec![0, 0, 0, 0, 0]);
        let expected = graphs
            .iter()
            .find(|g| g["name"] == name)
            .expect("Torch branch convention");
        close(
            &values,
            &serde_json::from_value::<Vec<f64>>(expected["expected"].clone())
                .expect("Torch values"),
        );
    }
    let hundred = "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0";
    let body = format!(
        "let tape=autodiff::new_tape(8,4);let cell=autodiff::new_cell();let x=autodiff::variable(tape,0.0);let big={hundred}*{hundred}*{hundred}*100000000.0;let h=autodiff::constant(tape,big);let a=autodiff::mul(tape,x,h);let b=autodiff::mul(tape,a,h);let ids:Vec<i64> = Vec::with_capacity(1);ids.push(x);let updates:Vec<f64> = Vec::with_capacity(1);updates.push(big);let before=alloc(0);let first=autodiff::backward(tape,a);let g1=autodiff::gradient_into(tape,x,cell);let saved=cell.value;let root=tape.last_root;let overflow=autodiff::backward(tape,b);let g2=autodiff::gradient_into(tape,x,cell);let kept=cell.value;let replay=autodiff::replay(tape,ids,updates);let g3=autodiff::gradient_into(tape,x,cell);let delta=alloc(0)-before;"
    );
    let fixture = Fixture::probe(
        &body,
        &[
            "first",
            "g1",
            "overflow",
            "g2",
            "replay",
            "g3",
            "root",
            "tape.last_root",
            "delta",
        ],
        &[
            "saved",
            "kept",
            "cell.value",
            "tape.values.get(0)",
            "tape.values.get(2)",
            "tape.values.get(3)",
        ],
    );
    let (state, values, _) = observe(&fixture, 9);
    assert_eq!(&state[..6], &[0, 0, -422, 0, -422, 0]);
    assert_eq!(state[6], state[7]);
    assert_eq!(state[8], 0);
    assert!(values[0].is_finite() && values[0] > 1e307);
    assert_eq!(values[0], values[1]);
    assert_eq!(values[0], values[2]);
    assert_eq!(&values[3..], &[0.0, 0.0, 0.0]);

    let replay = Fixture::probe(
        "let tape=autodiff::new_tape(8,4);let cell=autodiff::new_cell();let x=autodiff::variable(tape,3.0);let y=autodiff::mul(tape,x,x);let ids:Vec<i64> = Vec::with_capacity(1);ids.push(x);let updates:Vec<f64> = Vec::with_capacity(1);updates.push(4.0);let terms:Vec<i64> = Vec::with_capacity(2);terms.push(y);terms.push(y);let sum=autodiff::sum(tape,terms);terms.set(0,x);terms.set(1,x);let before=alloc(0);let first=autodiff::backward(tape,sum);let g1=autodiff::gradient_into(tape,x,cell);let one=cell.value;let updated=autodiff::replay(tape,ids,updates);let invalidated=autodiff::gradient_into(tape,x,cell);let second=autodiff::backward(tape,sum);let g2=autodiff::gradient_into(tape,x,cell);let two=cell.value;let read=autodiff::value_into(tape,sum,cell);let delta=alloc(0)-before;",
        &[
            "first",
            "g1",
            "updated",
            "invalidated",
            "second",
            "g2",
            "read",
            "delta",
        ],
        &["one", "two", "cell.value", "updates.get(0)"],
    );
    let (state, values, _) = observe(&replay, 8);
    assert_eq!(state, vec![0, 0, 0, -400, 0, 0, 0, 0]);
    assert_eq!(values, vec![12.0, 16.0, 32.0, 4.0]);
}

#[cfg(feature = "solver")]
fn mutate(fixture: &Fixture, needle: &str, replacement: &str) {
    let path = fixture.provider.join("src/autodiff.sigil");
    let original = std::fs::read_to_string(&path).expect("source");
    let changed = original.replacen(needle, replacement, 1);
    assert_ne!(original, changed, "live mutation site exists");
    std::fs::write(path, changed).expect("owned mutant");
    fixture.repin();
}
#[cfg(feature = "solver")]
#[test]
fn autodiff_live_mutants_and_confidential_parameters_are_detected() {
    let reference = reference();
    let graphs = reference["graphs"].as_array().expect("graphs");
    for (name, needle, replacement) in [
        (
            "square-3.0",
            "let updated = tape.scratch.get(parent) + value;",
            "let updated = value;",
        ),
        (
            "relu-0.0",
            "operation == 5 && tape.values.get(a) > 0.0",
            "operation == 5 && tape.values.get(a) >= 0.0",
        ),
        (
            "select-True",
            "if condition { chosen = yi; } else {}",
            "if !condition { chosen = yi; } else {}",
        ),
    ] {
        let case = graphs
            .iter()
            .find(|case| case["name"] == name)
            .expect("reference mutant target");
        let fixture = graph_probe(case, "");
        mutate(&fixture, needle, replacement);
        let (_, actual, _) = observe(&fixture, 4);
        let expected: Vec<f64> =
            serde_json::from_value(case["expected"].clone()).expect("Torch values");
        assert!(
            actual
                .iter()
                .zip(expected)
                .any(|(a, b)| (a - b).abs() > 1e-8),
            "live mutant {name} must be distinguishable"
        );
    }
    let repeated = Fixture::probe(
        "let tape=autodiff::new_tape(4,0);let cell=autodiff::new_cell();let x=autodiff::variable(tape,3.0);let y=autodiff::mul(tape,x,x);let first=autodiff::backward(tape,y);let second=autodiff::backward(tape,y);let read=autodiff::gradient_into(tape,x,cell);",
        &["first", "second", "read"],
        &["cell.value"],
    );
    mutate(
        &repeated,
        "tape.scratch.set(i, 0.0); i = i + 1;",
        "tape.scratch.set(i, tape.scratch.get(i)); i = i + 1;",
    );
    let (state, values, _) = observe(&repeated, 3);
    assert_eq!(state, vec![0, 0, 0]);
    assert_ne!(
        values,
        vec![6.0],
        "retained adjoints must be detected by repeated backward"
    );
    for label in ["Public", "Internal", "Secret"] {
        for (kind, ty, call) in [
            ("value", "f64", "autodiff::variable(tape,value)"),
            ("condition", "bool", "autodiff::select(tape,value,x,x)"),
        ] {
            let fixture = Fixture::new();
            let source = format!(
                "module tool;use sigil::autodiff;fn sample(value:{ty} @{label})->i64 @{label} ! {{Alloc}} {{let tape=autodiff::new_tape(4,0);let x=autodiff::variable(tape,2.0);return {call};}}pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return 0;}}"
            );
            std::fs::write(fixture.root.join("src/tool.sigil"), source).expect("label caller");
            fixture.lock();
            let output = cli(&fixture.root, "check", &[]);
            if label == "Public" {
                assert!(output.status.success(), "accept twin {kind}");
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
