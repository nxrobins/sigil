//! WHY THIS TEST EXISTS. Small native learning is not established by decreasing
//! printed loss: execute actual numeric packages against separately emitted Torch
//! float64 answers, observe memory, and kill wrong-gradient/update mutations.
//! The portable Unix test validates artifacts/locks; solver tests execute Wasm.

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

struct Fixture {
    directory: PathBuf,
    root: PathBuf,
    provider: PathBuf,
    with_fmt: bool,
}
impl Fixture {
    fn new() -> Self {
        let directory = loop {
            let path = std::env::temp_dir().join(format!(
                "sigil-numeric-{}-{}",
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
        let provider = directory.join("numeric");
        for (source, destination) in [
            (repo().join("library/programs/linear-regression"), &root),
            (repo().join("library/packages/numeric"), &provider),
        ] {
            std::fs::create_dir_all(destination.join("src")).expect("fresh source root");
            for entry in std::fs::read_dir(&source).expect("package files") {
                let entry = entry.expect("entry");
                if entry.file_type().expect("type").is_file()
                    && entry.file_name() != "sigil-package.lock.json"
                {
                    std::fs::copy(entry.path(), destination.join(entry.file_name()))
                        .expect("copy metadata");
                }
            }
            for entry in std::fs::read_dir(source.join("src")).expect("sources") {
                let entry = entry.expect("entry");
                assert!(entry.file_type().expect("type").is_file());
                std::fs::copy(
                    entry.path(),
                    destination.join("src").join(entry.file_name()),
                )
                .expect("copy source");
            }
        }
        // Preserve the executed handwired consumer as the numeric v1 regression
        // baseline. The current example is separately exercised by autodiff_tools.
        std::fs::write(
            root.join("src/tool.sigil"),
            include_str!(
                "../../../library/tests/fixtures/numeric/linear-regression-handwired.sigil"
            ),
        )
        .expect("preserved handwired baseline");
        let mut manifest = json(&root.join("sigil-package.json"));
        manifest["dependencies"]
            .as_array_mut()
            .expect("dependencies")
            .retain(|dependency| dependency["package"] == "sigil/numeric");
        std::fs::write(
            root.join("sigil-package.json"),
            serde_json::to_vec(&manifest).expect("legacy manifest"),
        )
        .expect("numeric-only baseline selection");
        Self {
            directory,
            root,
            provider,
            with_fmt: false,
        }
    }
    #[cfg(feature = "solver")]
    fn probe(source: &str) -> Self {
        let mut fixture = Self::new();
        fixture.with_fmt = true;
        std::fs::write(fixture.root.join("src/tool.sigil"), source)
            .expect("write observation driver");
        let mut manifest = json(&fixture.root.join("sigil-package.json"));
        let lock: serde_json::Value = serde_json::from_slice(
            &sigil_compiler::package::derive_local_package_lock(
                &repo().join("library/packages/fmt"),
            )
            .expect("read actual fmt identity"),
        )
        .expect("JSON");
        let node = &lock["nodes"][0];
        manifest["dependencies"].as_array_mut().expect("dependencies").push(serde_json::json!({"package":"sigil/fmt","requirement":format!("={}",node["version"].as_str().expect("version")),"source":"workspace","content_hash":node["content_hash"],"features":[],"default_features":false,"optional":false}));
        manifest["dependencies"]
            .as_array_mut()
            .expect("dependencies")
            .sort_by_key(|dependency| {
                dependency["package"]
                    .as_str()
                    .expect("package name")
                    .to_owned()
            });
        std::fs::write(
            fixture.root.join("sigil-package.json"),
            serde_json::to_vec(&manifest).expect("probe manifest"),
        )
        .expect("write owned probe declaration");
        fixture
    }
    fn lock(&self) -> Vec<u8> {
        let mut dependencies = vec![LocalPackageDependency {
            package: "sigil/numeric".into(),
            path: self.provider.clone(),
        }];
        if self.with_fmt {
            dependencies.push(LocalPackageDependency {
                package: "sigil/fmt".into(),
                path: repo().join("library/packages/fmt"),
            });
        }
        create_local_package_lock_with_dependencies(&self.root, &dependencies)
            .expect("derive actual locked graph")
    }
    #[cfg(feature = "solver")]
    fn compile(&self) -> sigil_compiler::package::PackageCompilation {
        self.lock();
        sigil_compiler::package::compile_local_package_with_context(
            &self.root,
            sigil_compiler::CompileOptions::default(),
            &sigil_compiler::CompilerContext::default(),
        )
        .expect("solver compile real numeric graph")
    }
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

#[test]
fn numeric_metadata_and_changed_cached_source_are_bound() {
    for (root, inventory) in [
        ("library/packages/numeric", "inputs.json"),
        ("library/programs/linear-regression", "tool-inputs.json"),
    ] {
        let root = repo().join(root);
        let manifest = json(&root.join("sigil-package.json"));
        for (field, file) in [
            ("api_card_hash", "api-card.json"),
            ("api_contract_hash", "API.md"),
            ("charter_hash", "README.md"),
            ("evidence_manifest_hash", inventory),
        ] {
            assert_eq!(
                manifest["evidence"][field],
                hash(&std::fs::read(root.join(file)).expect("actual file"))
            );
        }
        for (file, expected) in json(&root.join(inventory))["files"]
            .as_object()
            .expect("inventory")
        {
            let mut bytes = std::fs::read(root.join(file)).expect("bound input");
            assert_eq!(expected, &hash(&bytes));
            bytes.push(b'!');
            assert_ne!(expected, &hash(&bytes), "real changes break the binding");
        }
    }
    let fixture = Fixture::new();
    let lock = fixture.lock();
    let graph: serde_json::Value = serde_json::from_slice(&lock).expect("lock");
    assert_eq!(graph["nodes"].as_array().expect("nodes").len(), 2);
    let node = graph["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .find(|n| n["package"] == "sigil/numeric")
        .expect("numeric");
    std::fs::write(
        fixture
            .root
            .join(node["source"]["locator"].as_str().expect("locator"))
            .join("src/numeric.sigil"),
        "module numeric;\n",
    )
    .expect("plant changed cache");
    let output = cli(&fixture.root, "check", &[]);
    assert!(!output.status.success());
    assert_eq!(envelope(&output)["data"]["code"], "E_HASH_MISMATCH");
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
        1_000_000,
        10_000_000,
        16 * 1024 * 1024,
        &sigil_runtime::IoGrants::none(),
    )
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
fn floats(bytes: &[u8]) -> Vec<f64> {
    assert_eq!(bytes.len() % 8, 0);
    bytes
        .as_chunks::<8>()
        .0
        .iter()
        .map(|part| f64::from_le_bytes(*part))
        .collect()
}
#[cfg(feature = "solver")]
fn close(actual: &[f64], expected: &[f64]) {
    assert_eq!(actual.len(), expected.len());
    for (a, b) in actual.iter().zip(expected) {
        assert!(
            a.is_finite() && (a - b).abs() <= 1e-12 + 1e-11 * b.abs(),
            "actual {a:.17}, expected {b:.17}"
        );
    }
}
#[cfg(feature = "solver")]
fn probe(
    case: &serde_json::Value,
    extra: &str,
    call_override: Option<&str>,
    planted: &str,
) -> String {
    let mut source = String::from(
        "module tool; use sigil::numeric; use sigil::vec; use sigil::fmt;\npub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {Alloc} {\n",
    );
    for name in ["a", "b"] {
        let matrix = &case[name];
        let rows = matrix["rows"].as_i64().expect("rows");
        let cols = matrix["cols"].as_i64().expect("cols");
        source.push_str(&format!("let {name}=numeric::zeros({rows},{cols});\n"));
        for (i, value) in matrix["values"]
            .as_array()
            .expect("values")
            .iter()
            .enumerate()
        {
            source.push_str(&format!(
                "if numeric::set({name},{},{},{})<0 {{return -900;}} else {{}}\n",
                i as i64 / cols,
                i as i64 % cols,
                literal(value.as_f64().expect("float"))
            ));
        }
    }
    let rows = case["out_rows"].as_i64().expect("out rows");
    let cols = case["out_cols"].as_i64().expect("out cols");
    source.push_str(&format!("let out=numeric::zeros({rows},{cols}); let scalar=numeric::new_scalar(); scalar.value=77.0;\nlet mut i=0; while i<{} {{out.data.set(i,77.0);i=i+1;}}\n{extra}\n",rows*cols));
    let sizes = [
        case["a"]["values"].as_array().expect("a").len() * 8,
        case["b"]["values"].as_array().expect("b").len() * 8,
        (rows * cols * 8) as usize,
    ];
    let total: usize = sizes.iter().sum();
    source.push_str(&format!("let a_ptr=a.data.buf;let b_ptr=b.data.buf;let out_ptr=out.data.buf;let saved=alloc({total});\n"));
    let mut offset = 0;
    for (name, size) in ["a", "b", "out"].into_iter().zip(sizes) {
        source.push_str(&format!(
            "i=0;while i<{size} {{store8(saved+{offset}+i,load8({name}_ptr+i));i=i+1;}}\n"
        ));
        offset += size;
    }
    let operation = case["operation"].as_str().expect("operation");
    let call = call_override
        .map(str::to_owned)
        .unwrap_or_else(|| match operation {
            "scale_into" => "numeric::scale_into(a,0.0-0.75,out)".into(),
            "relu_into" | "transpose_into" => format!("numeric::{operation}(a,out)"),
            "sum_into" | "mean_into" => format!("numeric::{operation}(a,scalar)"),
            "dot_into" | "mse_into" => format!("numeric::{operation}(a,b,scalar)"),
            _ => format!("numeric::{operation}(a,b,out)"),
        });
    source.push_str(&format!(
        "let before=alloc(0);{planted}\nlet status={call};let delta=alloc(0)-before;\n"
    ));
    source.push_str(&format!("let cell:Vec<f64> =Vec::with_capacity(1);cell.push(scalar.value);let status_text=fmt::decimal_i64(status);let delta_text=fmt::decimal_i64(delta);let sp=status_text/4294967296;let sl=status_text-sp*4294967296;let dp=delta_text/4294967296;let dl=delta_text-dp*4294967296;let result=alloc(sl+dl+2+8+{total}*2);i=0;while i<sl {{store8(result+i,load8(sp+i));i=i+1;}}store8(result+sl,47);i=0;while i<dl {{store8(result+sl+1+i,load8(dp+i));i=i+1;}}store8(result+sl+1+dl,47);let payload=result+sl+dl+2;i=0;while i<8 {{store8(payload+i,load8(cell.buf+i));i=i+1;}}i=0;while i<{total} {{store8(payload+8+i,load8(saved+i));i=i+1;}}\n"));
    offset = 0;
    for (name, size) in ["a", "b", "out"].into_iter().zip(sizes) {
        source.push_str(&format!("i=0;while i<{size} {{store8(payload+8+{total}+{offset}+i,load8({name}_ptr+i));i=i+1;}}\n"));
        offset += size;
    }
    source.push_str(&format!("return result*4294967296+sl+dl+2+8+{total}*2;}}"));
    source
}
#[cfg(feature = "solver")]
struct Observation {
    status: i64,
    delta: i64,
    scalar: f64,
    before: Vec<u8>,
    after: Vec<u8>,
    fuel: u64,
}
#[cfg(feature = "solver")]
fn observe(fixture: &Fixture) -> Observation {
    let result = execute(&fixture.compile(), b"").expect("observation driver executes");
    let mut sections = result.output.splitn(3, |b| *b == b'/');
    let status = std::str::from_utf8(sections.next().expect("status"))
        .expect("ASCII")
        .parse()
        .expect("status integer");
    let delta = std::str::from_utf8(sections.next().expect("delta"))
        .expect("ASCII")
        .parse()
        .expect("delta integer");
    let payload = sections.next().expect("payload");
    let scalar = floats(&payload[..8])[0];
    let count = (payload.len() - 8) / 2;
    Observation {
        status,
        delta,
        scalar,
        before: payload[8..8 + count].to_vec(),
        after: payload[8 + count..].to_vec(),
        fuel: result.fuel_consumed,
    }
}
#[cfg(feature = "solver")]
fn cases() -> serde_json::Value {
    serde_json::from_str(include_str!(
        "../../../library/tests/fixtures/numeric/torch-v1.json"
    ))
    .expect("separately emitted Torch answers")
}
#[cfg(feature = "solver")]
fn small_case() -> serde_json::Value {
    serde_json::json!({"operation":"add_into","a":{"rows":1,"cols":2,"values":[1.0,2.0]},"b":{"rows":1,"cols":2,"values":[3.0,4.0]},"out_rows":1,"out_cols":2,"scalar":false})
}

#[cfg(feature = "solver")]
#[test]
fn numeric_operators_match_pytorch_float64_and_preserve_input_data_without_allocation() {
    let reference = cases();
    assert_eq!(reference["reference"]["torch"], "2.14.1");
    assert_eq!(reference["reference"]["dtype"], "float64");
    assert_eq!(reference["reference"]["device"], "cpu");
    let cases = reference["operations"].as_array().expect("operations");
    assert!(
        cases.len() >= 49,
        "measured reference corpus deletion floor"
    );
    let mut maximum = 0;
    for case in cases {
        let fixture = Fixture::probe(&probe(case, "", None, ""));
        let observed = observe(&fixture);
        assert_eq!(observed.status, 0, "{case}");
        assert_eq!(observed.delta, 0, "{case}");
        maximum = maximum.max(observed.fuel);
        let input_bytes = (case["a"]["values"].as_array().expect("a").len()
            + case["b"]["values"].as_array().expect("b").len())
            * 8;
        assert_eq!(
            &observed.before[..input_bytes],
            &observed.after[..input_bytes],
            "read-only operands remain byte-identical"
        );
        let expected: Vec<f64> =
            serde_json::from_value(case["expected"].clone()).expect("Torch values");
        close(
            &if case["scalar"] == true {
                vec![observed.scalar]
            } else {
                floats(&observed.after[input_bytes..])
            },
            &expected,
        );
    }
    eprintln!(
        "numeric: {} Torch float64 operator cases; whole-observer maximum SIGIL fuel {maximum}",
        cases.len()
    );
    assert!(maximum <= 1_500, "fixed reference observer fuel ceiling");
    let case = small_case();
    for (call, expected_a, expected_scalar) in [
        ("numeric::set(a,0,1,0.0-0.5)", vec![1.0, -0.5], 77.0),
        ("numeric::get_into(a,0,1,scalar)", vec![1.0, 2.0], 2.0),
        ("numeric::sgd_step(a,b,0.05)", vec![0.85, 1.8], 77.0),
    ] {
        let fixture = Fixture::probe(&probe(&case, "", Some(call), ""));
        let observed = observe(&fixture);
        assert_eq!(observed.status, 0, "{call}");
        assert_eq!(observed.delta, 0, "{call}");
        close(&floats(&observed.after[..16]), &expected_a);
        assert_eq!(observed.scalar, expected_scalar);
        assert_eq!(observed.before[16..], observed.after[16..]);
    }
    let shared_input = Fixture::probe(&probe(&case, "", Some("numeric::add_into(a,a,out)"), ""));
    let observed = observe(&shared_input);
    assert_eq!(observed.status, 0, "read-only inputs may alias one another");
    assert_eq!(observed.delta, 0);
    close(&floats(&observed.after[32..]), &[2.0, 4.0]);
    assert_eq!(observed.before[..32], observed.after[..32]);
    let allocating = Fixture::probe(&probe(&case, "", None, "let scratch=alloc(8);"));
    assert_eq!(observe(&allocating).delta, 8, "positive allocation control");
    let writing = Fixture::probe(&probe(&case, "", None, "a.data.set(0,99.0);"));
    let observed = observe(&writing);
    assert_ne!(
        observed.before[..16],
        observed.after[..16],
        "positive input-write control"
    );
}

#[cfg(feature = "solver")]
#[test]
fn numeric_errors_preserve_outputs_for_shape_alias_nonfinite_and_overflow() {
    let case = small_case();
    let mut scenarios = vec![
        (
            "out.data.buf=a.data.buf;",
            "numeric::add_into(a,b,out)",
            -400,
        ),
        (
            "out.data.buf=b.data.buf;",
            "numeric::add_into(a,b,out)",
            -400,
        ),
        (
            "out.data.buf=a.data.buf+8;",
            "numeric::add_into(a,b,out)",
            -400,
        ),
        (
            "b.data.buf=a.data.buf;",
            "numeric::sgd_step(a,b,0.05)",
            -400,
        ),
        ("", "numeric::sgd_step(a,b,0.0-0.1)", -422),
        ("", "numeric::sgd_step(a,b,1.0/0.0)", -422),
        ("", "numeric::get_into(a,-1,0,scalar)", -400),
        ("", "numeric::get_into(a,0,2,scalar)", -400),
        ("", "numeric::set(a,1,0,1.0)", -400),
        ("", "numeric::set(a,0,0,0.0/0.0)", -422),
        ("a.rows=2;", "numeric::add_into(a,b,out)", -400),
        ("b.cols=1;", "numeric::add_into(a,b,out)", -400),
        ("out.data.count=1;", "numeric::add_into(a,b,out)", -400),
        ("a.data.set(1,0.0/0.0);", "numeric::add_into(a,b,out)", -422),
        (
            "b.data.set(1,1.0/0.0);",
            "numeric::mse_into(a,b,scalar)",
            -422,
        ),
        ("b.rows=2;b.cols=1;", "numeric::add_into(a,b,out)", -422),
        ("", "numeric::matmul_into(a,b,out)", -422),
        ("", "numeric::transpose_into(a,out)", -422),
        ("", "numeric::zeros(0,1).error", -400),
        ("", "numeric::zeros(-1,1).error", -400),
        ("", "numeric::zeros(9223372036854775807,2).error", -413),
        ("", "numeric::zeros(65,64).error", -413),
    ];
    let huge = "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.0";
    let overflow = format!("let big={huge}*{huge}*{huge};a.data.set(1,big);b.data.set(1,big);");
    scenarios.push((&overflow, "numeric::mul_into(a,b,out)", -422));
    scenarios.push((&overflow, "numeric::scale_into(a,10000000000.0,out)", -422));
    for (extra, call, expected) in &scenarios {
        let fixture = Fixture::probe(&probe(&case, extra, Some(call), ""));
        let observed = observe(&fixture);
        assert_eq!(observed.status, *expected, "{call}");
        assert_eq!(
            observed.before, observed.after,
            "refusal preserves every actual buffer: {call}"
        );
        assert_eq!(observed.scalar, 77.0);
        if !call.contains("zeros(") {
            assert_eq!(observed.delta, 0);
        }
    }
    let limit = Fixture::probe(&probe(
        &case,
        "",
        Some("numeric::get_into(numeric::zeros(64,64),63,63,scalar)"),
        "",
    ));
    let observed = observe(&limit);
    assert_eq!(observed.status, 0);
    assert_eq!(observed.scalar, 0.0);
    eprintln!(
        "numeric: {} refusal cases plus exact 4096-element constructor/read boundary",
        scenarios.len()
    );
}

#[cfg(feature = "solver")]
fn mutate(fixture: &Fixture, needle: &str, replacement: &str) {
    let path = fixture.provider.join("src/numeric.sigil");
    let before = std::fs::read_to_string(&path).expect("source");
    let after = before.replacen(needle, replacement, 1);
    assert_ne!(before, after, "mutation site exists");
    std::fs::write(path, after).expect("plant owned mutation");
    let lock: serde_json::Value = serde_json::from_slice(
        &sigil_compiler::package::derive_local_package_lock(&fixture.provider)
            .expect("explicit mutant identity"),
    )
    .expect("JSON");
    let path = fixture.root.join("sigil-package.json");
    let mut manifest = json(&path);
    manifest["dependencies"]
        .as_array_mut()
        .expect("dependencies")
        .iter_mut()
        .find(|dependency| dependency["package"] == "sigil/numeric")
        .expect("numeric selection")["content_hash"] = lock["nodes"][0]["content_hash"].clone();
    std::fs::write(path, serde_json::to_vec(&manifest).expect("encode"))
        .expect("pin only test mutant");
}

#[cfg(feature = "solver")]
#[test]
fn numeric_wrong_gradients_updates_and_public_label_violations_are_detected() {
    // Directly reusing a frozen argument as mutable is already rejected by the
    // compiler. The runtime overlap cases separately exercise distinct records
    // whose backing spans have been made to overlap by an adversarial caller.
    for call in ["numeric::add_into(a,b,a)", "numeric::sgd_step(a,a,0.05)"] {
        let fixture = Fixture::probe(&probe(&small_case(), "", Some(call), ""));
        fixture.lock();
        let output = cli(&fixture.root, "check", &[]);
        assert!(!output.status.success());
        let value = envelope(&output);
        assert!(
            value["diagnostics"]
                .as_array()
                .expect("diagnostics")
                .iter()
                .any(|diagnostic| diagnostic["code"] == "T255")
        );
    }
    let reference = cases();
    let case = reference["operations"]
        .as_array()
        .expect("cases")
        .iter()
        .find(|case| {
            case["operation"] == "mse_grad_into"
                && case["a"]["values"].as_array().expect("values").len() > 1
        })
        .expect("nonzero multielement gradient");
    let mut losses = Vec::new();
    for perturbation in [-0.0001, 0.0001] {
        let mut shifted = case.clone();
        shifted["operation"] = "mse_into".into();
        shifted["scalar"] = true.into();
        let value = shifted["a"]["values"][0].as_f64().expect("finite input");
        shifted["a"]["values"][0] = (value + perturbation).into();
        let fixture = Fixture::probe(&probe(&shifted, "", None, ""));
        let observed = observe(&fixture);
        assert_eq!(observed.status, 0);
        losses.push(observed.scalar);
    }
    let finite_difference = (losses[1] - losses[0]) / 0.0002;
    assert!(
        (finite_difference - case["expected"][0].as_f64().expect("Torch derivative")).abs() < 1e-7,
        "native MSE finite difference independently checks the gradient convention"
    );
    let fixture = Fixture::probe(&probe(case, "", None, ""));
    mutate(
        &fixture,
        "let factor = 2.0 / count_float(prediction.data.count);",
        "let factor = 1.0 / count_float(prediction.data.count);",
    );
    let observed = observe(&fixture);
    let offset = (case["a"]["values"].as_array().expect("a").len()
        + case["b"]["values"].as_array().expect("b").len())
        * 8;
    let actual = floats(&observed.after[offset..]);
    let expected: Vec<f64> = serde_json::from_value(case["expected"].clone()).expect("gradient");
    assert!(
        actual
            .iter()
            .zip(expected)
            .any(|(a, b)| (a - b).abs() > 1e-8),
        "live half-gradient mutant must disagree"
    );
    for label in ["Public", "Internal", "Secret"] {
        for operation in ["set", "sgd_step", "scale_into"] {
            let call = if operation == "set" {
                "numeric::set(a,0,0,value)"
            } else if operation == "scale_into" {
                "numeric::scale_into(a,value,b)"
            } else {
                "numeric::sgd_step(a,b,value)"
            };
            let source = format!(
                "module tool;use sigil::numeric;fn sample(value:f64 @{label})->i64 @{label} ! {{Alloc}} {{let a=numeric::zeros(1,1);let b=numeric::zeros(1,1);return {call};}} pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return 0;}}"
            );
            let fixture = Fixture::new();
            std::fs::write(fixture.root.join("src/tool.sigil"), source).expect("labeled caller");
            fixture.lock();
            let output = cli(&fixture.root, "check", &[]);
            if label == "Public" {
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stdout)
                );
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
    let fixture = Fixture::new();
    mutate(
        &fixture,
        "weights.data.get(i) - rate * gradient.data.get(i)",
        "weights.data.get(i) + rate * gradient.data.get(i)",
    );
    // The first replacement affects the validation pass; mutate the writing pass
    // separately so the experiment actually executes a wrong update.
    mutate(
        &fixture,
        "weights.data.set(i, weights.data.get(i) - rate * gradient.data.get(i));",
        "weights.data.set(i, weights.data.get(i) + rate * gradient.data.get(i));",
    );
    let result = execute(&fixture.compile(), b"1").expect("live wrong-sign update");
    assert!(
        floats(&result.output)[1] > 21.0,
        "wrong-sign SGD must increase this loss"
    );
}

#[cfg(feature = "solver")]
#[test]
fn numeric_native_training_matches_torch_and_refuses_stale_evidence_and_budgets() {
    let fixture = Fixture::new();
    let package = fixture.compile();
    let reference = cases();
    let mut fuel = 0;
    for case in reference["training"].as_array().expect("training") {
        let input = case["epochs"].to_string();
        let result = execute(&package, input.as_bytes()).expect("native training executes");
        let expected: Vec<f64> =
            serde_json::from_value(case["expected"].clone()).expect("Torch training result");
        close(&floats(&result.output), &expected);
        fuel = fuel.max(result.fuel_consumed);
    }
    assert!(
        fuel <= 80_000,
        "bounded 0..200-step reference training fuel"
    );
    let result = execute(&package, b"100").expect("default workload");
    let values = floats(&result.output);
    assert!(values[1] < 0.00001 && values[8] < 0.0001);
    assert_eq!(
        execute(&package, b"").expect("default epochs").output,
        result.output
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
            "bad epochs refuse {input:?}"
        );
    }
    let certificate = fixture.directory.join("training.cert.json");
    let cert = certificate.to_str().expect("path");
    let checked = cli(&fixture.root, "check", &["--cert", cert]);
    assert!(checked.status.success());
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
    let shown: serde_json::Value = serde_json::from_slice(&viewer.stdout).expect("viewer JSON");
    assert!((shown["bias"].as_f64().expect("bias") - values[2]).abs() < 1e-15);
    let path = fixture.root.join("src/tool.sigil");
    let original = std::fs::read_to_string(&path).expect("source");
    std::fs::write(
        &path,
        original.replace("let mut epochs = 100;", "let mut epochs = 99;"),
    )
    .expect("edit source");
    let stale_source = cli(&fixture.root, "run", &["--input", "100", "--cert", cert]);
    assert!(!stale_source.status.success());
    assert_eq!(envelope(&stale_source)["data"]["code"], "E_HASH_MISMATCH");
    let old_certificate = std::fs::read(&certificate).expect("retain old certificate");
    std::fs::rename(
        fixture.root.join("sigil-package.lock.json"),
        fixture.directory.join("before-source-change.lock.json"),
    )
    .expect("preserve old root lock before explicit relock");
    fixture.lock();
    let stale_certificate = cli(&fixture.root, "run", &["--input", "100", "--cert", cert]);
    assert!(!stale_certificate.status.success());
    assert_eq!(
        envelope(&stale_certificate)["data"]["code"],
        "E_CERTIFICATE"
    );
    assert_eq!(
        std::fs::read(&certificate).expect("certificate"),
        old_certificate
    );
    eprintln!(
        "numeric training: six Torch comparisons; 100-step fuel {}, max sampled 0..200-step fuel {fuel}; Wasm {} bytes",
        result.fuel_consumed,
        package.compilation.wasm_inner.len()
    );
    let allocating = Fixture::new();
    let path = allocating.root.join("src/tool.sigil");
    let text = std::fs::read_to_string(&path).expect("source");
    std::fs::write(
        path,
        text.replace(
            "while step < epochs {",
            "while step < epochs { let scratch=alloc(8);",
        ),
    )
    .expect("plant real loop allocation");
    assert!(
        matches!(
            execute(&allocating.compile(), b"1"),
            Err(sigil_runtime::ToolError::Trapped { .. })
        ),
        "allocation fence must refuse an actual growing loop"
    );
}
