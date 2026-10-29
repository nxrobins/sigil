//! WHY THIS TEST EXISTS. Staged updates must preserve accepted parameters on
//! refusal, and the real autoresearch fitter must agree with independent Torch.
//! Execute imported packages, bound their inputs, and kill live semantic faults.
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
}
impl Fixture {
    fn new() -> Self {
        let directory = loop {
            let candidate = std::env::temp_dir().join(format!(
                "sigil-optim-{}-{}",
                std::process::id(),
                SEQUENCE.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&candidate) {
                Ok(()) => break candidate,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("owned fixture: {e}"),
            }
        };
        let root = directory.join("consumer");
        copy(&repo().join("library/programs/autoresearch"), &root);
        for name in [
            "optim",
            "numeric",
            "autodiff",
            "records",
            "json",
            "rng",
            "checkpoint",
            "exchange",
        ] {
            copy(
                &repo().join("library/packages").join(name),
                &directory.join(name),
            );
        }
        copy(
            &repo().join("library/packages/bytes/versions/0.1.0-public.5"),
            &directory.join("bytes"),
        );
        Self { directory, root }
    }
    fn dependency(&self, name: &str) -> LocalPackageDependency {
        LocalPackageDependency {
            package: format!("sigil/{name}"),
            path: self.directory.join(name),
        }
    }
    fn lock(&self) -> Vec<u8> {
        create_local_package_lock_with_dependencies(
            &self.root,
            &[
                self.dependency("optim"),
                self.dependency("numeric"),
                self.dependency("autodiff"),
                self.dependency("records"),
                self.dependency("json"),
                self.dependency("rng"),
                self.dependency("bytes"),
                self.dependency("checkpoint"),
                self.dependency("exchange"),
            ],
        )
        .expect("fresh ten-node graph")
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
        let fixture = Self::new();
        std::fs::write(
            fixture.root.join("src/tool.sigil"),
            format!(
                "module tool;use sigil::optim;use sigil::numeric;use sigil::vec;
            pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{
            let observations:Vec<f64> = Vec::with_capacity(64);{body}
            let output=alloc(observations.len()*8);let mut j=0;
            while j<observations.len()*8 {{store8(output+j,load8(observations.buf+j));j=j+1;}}
            return output*4294967296+observations.len()*8;}}"
            ),
        )
        .expect("executable probe");
        fixture
    }
    #[cfg(feature = "solver")]
    fn mutate(&self, provider: bool, needle: &str, replacement: &str) {
        let path = if provider {
            self.directory.join("optim/src/optim.sigil")
        } else {
            self.root.join("src/tool_fit.sigil")
        };
        let source = std::fs::read_to_string(&path).expect("source");
        assert_eq!(source.matches(needle).count(), 1, "unique mutation site");
        std::fs::write(path, source.replacen(needle, replacement, 1)).expect("owned mutant");
        if provider {
            let graph: serde_json::Value = serde_json::from_slice(
                &create_local_package_lock_with_dependencies(
                    &self.directory.join("optim"),
                    &[self.dependency("numeric")],
                )
                .expect("mutant identity"),
            )
            .expect("graph");
            let identity = &graph["nodes"]
                .as_array()
                .expect("nodes")
                .iter()
                .find(|node| node["package"] == "sigil/optim")
                .expect("optim")["content_hash"];
            let mut manifest = json(&self.root.join("sigil-package.json"));
            let pin = manifest["dependencies"]
                .as_array_mut()
                .expect("dependencies")
                .iter_mut()
                .find(|dep| dep["package"] == "sigil/optim")
                .expect("pin");
            pin["content_hash"] = identity.clone();
            std::fs::write(
                self.root.join("sigil-package.json"),
                serde_json::to_vec(&manifest).expect("encode"),
            )
            .expect("owned mutant pin");
        }
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

fn duplicate_helpers(source: &str) -> std::collections::BTreeSet<&'static str> {
    let compact = source.split_whitespace().collect::<String>();
    let mut found = std::collections::BTreeSet::new();
    for (name, pattern) in [
        ("hex decoder", "fnnibble("),
        ("random stream", "fnrng_next("),
        ("bounded random", "fnrng_below("),
        ("signed random", "fnrng_signed("),
    ] {
        if compact.contains(pattern) {
            found.insert(name);
        }
    }
    if compact.split("store8(").skip(1).any(|tail| {
        tail.split(';')
            .next()
            .expect("first segment")
            .contains("load8(")
    }) {
        found.insert("raw byte copying");
    }
    found
}

#[test]
fn autoresearch_consumer_retires_known_helpers_and_uses_shared_packages() {
    let root = repo().join("library/programs/autoresearch");
    let manifest = json(&root.join("sigil-package.json"));
    let source = manifest["modules"]
        .as_array()
        .expect("modules")
        .iter()
        .map(|m| {
            std::fs::read_to_string(root.join(format!("src/{}.sigil", m.as_str().expect("module"))))
                .expect("consumer source")
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(duplicate_helpers(&source).is_empty());
    // Scope is the named legacy helpers and literal byte-copy idiom, not an
    // assertion that arbitrary renamed code cannot duplicate an implementation.
    for (name, body) in [
        ("hex decoder", "fn nibble(byte:i64)->i64 {return 0;}"),
        ("random stream", "fn rng_next(r:Rng)->i64 {return 0;}"),
        (
            "bounded random",
            "fn rng_below(r:Rng,n:i64)->i64 {return 0;}",
        ),
        (
            "signed random",
            "fn rng_signed(r:Rng,n:i64)->i64 {return 0;}",
        ),
        ("raw byte copying", "store8(dst + i,\n load8(src + i));"),
    ] {
        assert_eq!(
            duplicate_helpers(&format!("{source}\n{body}")),
            std::collections::BTreeSet::from([name])
        );
    }
    for call in [
        "autodiff::backward(",
        "numeric::zeros(",
        "optim::begin_sign(",
        "rng::below(",
        "records::unhex(",
        "bytes::copy_into(",
        "checkpoint::advance(",
        "exchange::open_response(",
    ] {
        assert!(source.contains(call), "consumer must call {call}");
        assert!(
            !source.replace(call, "removed_call(").contains(call),
            "live dependency-use detector"
        );
    }
}

#[test]
fn optim_fitting_inputs_and_fresh_dependency_graph_are_bound() {
    for (directory, inventory) in [
        ("library/packages/optim", "inputs.json"),
        ("library/programs/autoresearch", "tool-inputs.json"),
    ] {
        let root = repo().join(directory);
        let manifest = json(&root.join("sigil-package.json"));
        let card = json(&root.join("api-card.json"));
        assert_eq!(card["version"], manifest["version"]);
        assert_eq!(
            card["package"],
            format!(
                "{}/{}",
                manifest["namespace"].as_str().expect("namespace"),
                manifest["name"].as_str().expect("name")
            )
        );
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
            let mut bytes = std::fs::read(root.join(file)).expect("input");
            assert_eq!(expected, &hash(&bytes));
            bytes.push(b'!');
            assert_ne!(expected, &hash(&bytes), "live drift");
        }
    }
    let fixture = Fixture::new();
    let lock = fixture.lock();
    let graph: serde_json::Value = serde_json::from_slice(&lock).expect("graph");
    let nodes = graph["nodes"].as_array().expect("nodes");
    assert_eq!(nodes.len(), 10);
    let provider = nodes
        .iter()
        .find(|node| node["package"] == "sigil/optim")
        .expect("optim");
    let cached = fixture
        .root
        .join(provider["source"]["locator"].as_str().expect("cache"));
    std::fs::write(cached.join("src/optim.sigil"), "module optim;\n").expect("live drift");
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
fn search_input(command: &[u8; 4], payload: &[u8]) -> Vec<u8> {
    let mut bytes = command.to_vec();
    bytes.extend_from_slice(&[1, 0, 0, 0]);
    bytes.extend_from_slice(payload);
    bytes
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
        .into_bytes()
}
#[cfg(feature = "solver")]
fn search_start(seed: u64, generations: u8, steps: u8, hybrid: bool, budget: u64) -> Vec<u8> {
    let mut bytes = b"ASIN".to_vec();
    bytes.extend_from_slice(&[1, generations, steps, u8::from(hybrid)]);
    for value in [seed, 54, budget] {
        bytes.extend_from_slice(&value.to_le_bytes());
    }
    bytes
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
        .into_bytes()
}

#[cfg(feature = "solver")]
fn exchange_message(request: &[u8], status: u64, report: &[u8]) -> Vec<u8> {
    let hex = |raw: &[u8]| raw.iter().map(|b| format!("{b:02x}")).collect::<String>();
    format!("{{\"format\":\"sigil-evaluation-response-v1\",\"request_hex\":\"{}\",\"status\":\"{status:016x}\",\"payload_hex\":\"{}\"}}",hex(request),hex(report)).into_bytes()
}

#[cfg(feature = "solver")]
fn exchange_worker(
    package: &sigil_compiler::package::PackageCompilation,
    request: &[u8],
) -> sigil_runtime::ToolResult {
    let raw = execute(package, &search_input(b"ASED", request))
        .expect("native worker request")
        .output;
    let encoded = raw.iter().map(|b| format!("{b:02x}")).collect::<String>();
    let report = execute(package, encoded.as_bytes())
        .expect("bounded native fitter")
        .output;
    let mut payload = (request.len() as u16).to_le_bytes().to_vec();
    payload.push(0);
    payload.extend_from_slice(request);
    payload.extend_from_slice(&report);
    execute(package, &search_input(b"ASER", &payload)).expect("bounded native response")
}

#[cfg(feature = "solver")]
#[test]
fn composed_exchange_matches_every_independent_search_transition() {
    let package = Fixture::new().compile();
    let oracle = json(&repo().join("library/tests/fixtures/autoresearch-search/torch-pcg-v1.json"));
    let identity = [0xa5; 64];
    let mut count = 0;
    let mut peak = 0;
    for case in oracle["cases"].as_array().expect("cases") {
        let states = case["states"].as_array().expect("trajectory");
        let mut snapshot = unhex(states[0].as_str().expect("initial state"));
        for reference in states.iter().skip(1) {
            let next = if search_word(&snapshot, 12) == 1 {
                execute(&package, &search_input(b"ASST", &snapshot)).expect("local breeding")
            } else {
                let input = search_input(b"ASEQ", &[identity.as_slice(), &snapshot].concat());
                let request = execute(&package, &input).expect("native request").output;
                assert_eq!(
                    execute(&package, &input)
                        .expect("stable retry identity")
                        .output,
                    request
                );
                let response = exchange_worker(&package, &request);
                peak = peak.max(response.fuel_consumed);
                let received = execute(
                    &package,
                    &search_input(
                        b"ASEA",
                        &[identity.as_slice(), &snapshot, &response.output].concat(),
                    ),
                )
                .expect("matched response");
                peak = peak.max(received.fuel_consumed);
                count += 1;
                received
            };
            snapshot = next.output;
            assert!(
                search_matches(&snapshot, &unhex(reference.as_str().expect("state"))),
                "exchange must follow independent Torch/C trajectory"
            );
        }
        search_refuses(
            execute(
                &package,
                &search_input(b"ASEQ", &[identity.as_slice(), &snapshot].concat()),
            ),
            409,
        );
    }
    assert_eq!(count, 128);
    println!("exchange: {count} CPU replies, peak cooperative fuel={peak}");
}

#[cfg(feature = "solver")]
#[test]
fn composed_exchange_refusals_preserve_retry_and_checkpoint_identity() {
    let package = Fixture::new().compile();
    let identity = [0xa5; 64];
    let initial = search_start(42, 1, 20, true, 16);
    let snapshot = execute(&package, &initial).expect("initial").output;
    let expected = execute(
        &package,
        &search_input(b"ASEQ", &[identity.as_slice(), &snapshot].concat()),
    )
    .expect("request")
    .output;
    let response = exchange_worker(&package, &expected).output;
    let record: serde_json::Value = serde_json::from_slice(&response).expect("reply");
    let report = unhex(record["payload_hex"].as_str().expect("body"));
    let accept = |s: &[u8], id: &[u8], reply: &[u8]| {
        execute(&package, &search_input(b"ASEA", &[id, s, reply].concat()))
    };
    let accepted = accept(&snapshot, &identity, &response)
        .expect("accept twin")
        .output;
    for status in 1..=4 {
        search_refuses(
            accept(
                &snapshot,
                &identity,
                &exchange_message(&expected, status, b""),
            ),
            502,
        );
    }
    for offset in [0, 32] {
        let mut changed = identity;
        changed[offset] ^= 1;
        search_refuses(accept(&snapshot, &changed, &response), 409);
    }
    search_refuses(accept(&accepted, &identity, &response), 409);
    // Structurally valid envelopes cannot smuggle inconsistent fitting results.
    for (offset, value, code) in [
        (0, 2_u64, 409),
        (32, 7, 422),
        (40, 99, 422),
        (64, f64::NAN.to_bits(), 422),
        (88, 123.0_f64.to_bits(), 422),
        (264, 2, 422),
        (312, 1.0_f64.to_bits(), 422),
    ] {
        let mut changed = report.clone();
        changed[offset..offset + 8].copy_from_slice(&value.to_le_bytes());
        search_refuses(
            accept(
                &snapshot,
                &identity,
                &exchange_message(&expected, 0, &changed),
            ),
            code,
        );
    }
    let mut changed = report.clone();
    changed[840] ^= 1;
    search_refuses(
        accept(
            &snapshot,
            &identity,
            &exchange_message(&expected, 0, &changed),
        ),
        409,
    );
    search_refuses(
        accept(
            &snapshot,
            &identity,
            &exchange_message(&expected, 0, &report[..report.len() - 1]),
        ),
        422,
    );
    assert_eq!(
        accept(&snapshot, &identity, &response)
            .expect("refusals do not consume a revision")
            .output,
        accepted
    );
    let checkpoint = execute(&package, &search_input(b"ASCK", &snapshot))
        .expect("checkpoint")
        .output;
    let raw_initial = unhex(std::str::from_utf8(&initial).expect("hex"));
    let restored = execute(
        &package,
        &search_input(b"ASOP", &[raw_initial, checkpoint].concat()),
    )
    .expect("restore")
    .output;
    assert_eq!(
        execute(
            &package,
            &search_input(b"ASEQ", &[identity.as_slice(), &restored].concat())
        )
        .expect("restored request")
        .output,
        expected
    );
    let zero = execute(&package, &search_start(42, 1, 20, true, 0))
        .expect("zero budget")
        .output;
    search_refuses(
        execute(
            &package,
            &search_input(b"ASEQ", &[identity.as_slice(), &zero].concat()),
        ),
        413,
    );
}

#[cfg(feature = "solver")]
#[test]
fn composed_exchange_maximum_candidate_and_failed_worker_keep_limits() {
    let package = Fixture::new().compile();
    let identity = [0x17; 64];
    let mut snapshot = execute(&package, &search_start(42, 1, 20, true, 16))
        .expect("initial")
        .output;
    snapshot[262] = 12;
    for index in 0..11 {
        snapshot[328 + index * 4..332 + index * 4].copy_from_slice(&[0, 4, 3, 1]);
    }
    snapshot[372..376].copy_from_slice(&[4, 14, 0, 0]);
    let expected = execute(
        &package,
        &search_input(b"ASEQ", &[identity.as_slice(), &snapshot].concat()),
    )
    .expect("request")
    .output;
    let work = search_input(b"ASED", &expected);
    let result = exchange_worker(&package, &expected);
    let received = execute(
        &package,
        &search_input(
            b"ASEA",
            &[identity.as_slice(), &snapshot, &result.output].concat(),
        ),
    )
    .expect("maximum receive");
    assert_eq!(
        received.output,
        execute(&package, &search_input(b"ASST", &snapshot))
            .expect("local twin")
            .output
    );
    println!(
        "maximum exchange worker fuel={}, receive={}",
        result.fuel_consumed, received.fuel_consumed
    );
    for (fuel, engine, memory) in [
        (1, 10_000_000, 16 * 1024 * 1024),
        (500_000, 1, 16 * 1024 * 1024),
        (500_000, 10_000_000, 1),
    ] {
        assert!(
            sigil_runtime::execute_ephemeral_with_budgets(
                &package.compilation.wasm_inner,
                &work,
                fuel,
                engine,
                memory,
                &sigil_runtime::IoGrants::none()
            )
            .is_err()
        );
    }
    let text = String::from_utf8(expected).expect("JSON");
    let bad = text.replace("41435055", "42435055");
    assert_ne!(bad, text);
    let raw = execute(&package, &search_input(b"ASED", bad.as_bytes()))
        .expect("data-only request")
        .output;
    let encoded = raw.iter().map(|b| format!("{b:02x}")).collect::<String>();
    search_refuses(execute(&package, encoded.as_bytes()), 422);
    let mut payload = (bad.len() as u16).to_le_bytes().to_vec();
    payload.push(1);
    payload.extend_from_slice(bad.as_bytes());
    let failed = execute(&package, &search_input(b"ASER", &payload))
        .expect("candidate refusal envelope")
        .output;
    let status: serde_json::Value = serde_json::from_slice(&failed).expect("JSON");
    assert_eq!(status["status"], "0000000000000001");
    assert_eq!(status["payload_hex"], "");
}
#[cfg(feature = "solver")]
fn search_word(state: &[u8], index: usize) -> u64 {
    u64::from_le_bytes(
        state[index * 8..index * 8 + 8]
            .try_into()
            .expect("state word"),
    )
}

#[cfg(feature = "solver")]
fn search_refuses(result: Result<sigil_runtime::ToolResult, sigil_runtime::ToolError>, code: u16) {
    assert!(
        matches!(&result, Err(sigil_runtime::ToolError::Trapped { message })
        if message == &format!("tool returned error ({code})")),
        "{result:?}"
    );
}

#[cfg(feature = "solver")]
#[test]
fn composed_search_replays_both_arms_and_preserves_complete_state() {
    let package = Fixture::new().compile();
    for hybrid in [false, true] {
        let start = search_start(42, 2, 20, hybrid, 24);
        let mut state = execute(&package, &start).expect("initialize").output;
        assert_eq!(state.len(), 1736);
        assert_eq!(
            state,
            execute(&package, &start).expect("repeat initialize").output
        );
        let mut peak = 0;
        let mut seen_breeding = 0;
        while search_word(&state, 12) != 2 {
            let before = state.clone();
            let request = search_input(b"ASST", &state);
            let next = execute(&package, &request).expect("bounded search step");
            peak = peak.max(next.fuel_consumed);
            assert_eq!(
                before,
                execute(&package, &search_input(b"ASVA", &before))
                    .expect("saved state valid")
                    .output
            );
            assert_eq!(
                next.output,
                execute(&package, &request)
                    .expect("resume in fresh instance")
                    .output
            );
            assert_eq!(search_word(&next.output, 13), search_word(&state, 13) + 1);
            if search_word(&state, 12) == 1 {
                seen_breeding += 1;
            }
            state = next.output;
        }
        assert_eq!(seen_breeding, 2);
        assert_eq!(search_word(&state, 13), 26);
        assert_eq!(search_word(&state, 14), 24);
        assert_eq!(search_word(&state, 19), 3);
        search_refuses(execute(&package, &search_input(b"ASST", &state)), 409);
        if hybrid {
            assert!(search_word(&state, 17) + search_word(&state, 18) > 0);
        } else {
            assert_eq!((search_word(&state, 17), search_word(&state, 18)), (0, 0));
        }
        println!("search hybrid={hybrid}: 26 transitions, peak cooperative fuel={peak}");
    }
}

#[cfg(feature = "solver")]
#[test]
fn composed_search_refuses_corrupt_state_and_exhausted_budget() {
    let package = Fixture::new().compile();
    let initial = execute(&package, &search_start(42, 1, 20, true, 1))
        .expect("initial state")
        .output;
    let scored = execute(&package, &search_input(b"ASST", &initial))
        .expect("one allowed candidate")
        .output;
    search_refuses(execute(&package, &search_input(b"ASST", &scored)), 413);
    assert_eq!(
        execute(&package, &search_input(b"ASVA", &scored))
            .expect("previous snapshot intact")
            .output,
        scored
    );
    for (offset, value) in [
        (0, 0),
        (6 * 8, 2),
        (7 * 8, 41),
        (8 * 8, 21),
        (9 * 8, 2),
        (10 * 8, 2),
        (11 * 8, 9),
        (12 * 8, 3),
        (13 * 8, 2),
        (14 * 8, 2),
        (16 * 8, 99),
        (19 * 8, 1),
        (20 * 8, 1),
        (256, 0),
        (256 + 5, 19),
        (256 + 6, 13),
        (256 + 73, 0),
        (256 + 119, 1),
        (256 + 120, 3),
        (256 + 121, 1),
        (1408, 1),
    ] {
        let mut bad = initial.clone();
        bad[offset] = value;
        assert_ne!(bad, initial, "live malformed state");
        let code = if offset == 0 {
            409
        } else if [56, 64, 72].contains(&offset) {
            413
        } else {
            422
        };
        search_refuses(execute(&package, &search_input(b"ASVA", &bad)), code);
    }
    let mut bad = initial.clone();
    bad[264..272].copy_from_slice(&f64::NAN.to_le_bytes());
    search_refuses(execute(&package, &search_input(b"ASVA", &bad)), 422);
    search_refuses(
        execute(&package, &search_input(b"ASST", &initial[..1735])),
        422,
    );
}

#[cfg(feature = "solver")]
fn search_matches(actual: &[u8], expected: &[u8]) -> bool {
    if actual.len() != 1736 || expected.len() != 1736 || actual[..256] != expected[..256] {
        return false;
    }
    for index in 0..8 {
        let start = 256 + index * 144;
        if actual[start..start + 8] != expected[start..start + 8]
            || actual[start + 72..start + 128] != expected[start + 72..start + 128]
        {
            return false;
        }
    }
    let ranges = (0..8)
        .flat_map(|i| {
            [
                256 + i * 144 + 8..256 + i * 144 + 72,
                256 + i * 144 + 128..256 + i * 144 + 144,
            ]
        })
        .chain(std::iter::once(1408..1736));
    ranges.into_iter().all(|range| {
        floats(&actual[range.clone()])
            .iter()
            .zip(floats(&expected[range]))
            .all(|(a, b)| {
                a.is_finite() && b.is_finite() && (a - b).abs() <= 1e-10 + 1e-10 * b.abs()
            })
    })
}

#[cfg(feature = "solver")]
#[test]
fn composed_search_checkpoint_restore_matches_uninterrupted_and_refuses_other_jobs() {
    let fixture = Fixture::new();
    let package = fixture.compile();
    let initial = search_start(42, 2, 20, true, 24);
    let config = unhex(std::str::from_utf8(&initial).expect("hex"));
    let mut state = execute(&package, &initial).expect("initial").output;
    let mut envelope = execute(&package, &search_input(b"ASCK", &state))
        .expect("initial checkpoint")
        .output;
    let mut peak = 0;
    for revision in 0..=26 {
        let destination = fixture
            .directory
            .join(format!("checkpoint-{revision}.json"));
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&destination)
            .expect("new checkpoint");
        file.write_all(&envelope).expect("checkpoint bytes");
        drop(file);
        assert!(
            std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&destination)
                .is_err(),
            "previous state cannot be overwritten"
        );
        let saved = std::fs::read(&destination).expect("fresh restoration bytes");
        let mut restore = config.clone();
        restore.extend_from_slice(&saved);
        assert_eq!(
            execute(&package, &search_input(b"ASOP", &restore))
                .expect("restore whole search")
                .output,
            state
        );
        let mut wrong = restore.clone();
        wrong[8] ^= 1;
        search_refuses(execute(&package, &search_input(b"ASOP", &wrong)), 409);
        let mut stale = state.clone();
        stale.extend_from_slice(&saved);
        search_refuses(execute(&package, &search_input(b"ASAD", &stale)), 409);
        assert_eq!(
            std::fs::read(&destination).expect("preserved snapshot"),
            saved
        );
        if revision == 26 {
            break;
        }
        let next = execute(&package, &search_input(b"ASST", &state))
            .expect("next search transition")
            .output;
        let mut publish = next.clone();
        publish.extend_from_slice(&saved);
        let result = execute(&package, &search_input(b"ASAD", &publish))
            .expect("advance checkpoint under unchanged budgets");
        peak = peak.max(result.fuel_consumed);
        envelope = result.output;
        let record: serde_json::Value = serde_json::from_slice(&envelope).expect("native JSON");
        assert_eq!(
            unhex(record["previous_hex"].as_str().expect("previous")),
            state
        );
        assert_eq!(
            unhex(record["current_hex"].as_str().expect("current")),
            next
        );
        state = next;
    }
    let reference =
        json(&repo().join("library/tests/fixtures/autoresearch-search/torch-pcg-v1.json"));
    let expected = reference["cases"][1]["states"]
        .as_array()
        .expect("trajectory")
        .last()
        .expect("final");
    assert!(search_matches(
        &state,
        &unhex(expected.as_str().expect("wire"))
    ));
    println!(
        "search checkpoint: {} bytes; peak cooperative fuel={peak}",
        envelope.len()
    );
}

#[cfg(feature = "solver")]
#[test]
fn composed_search_matches_independent_torch_and_upstream_pcg_at_every_transition() {
    let oracle = json(&repo().join("library/tests/fixtures/autoresearch-search/torch-pcg-v1.json"));
    let cases = oracle["cases"].as_array().expect("reference cases");
    assert_eq!(cases.len(), 6);
    let package = Fixture::new().compile();
    let mut transitions = 0;
    for case in cases {
        let expected = case["states"].as_array().expect("trajectory");
        let start = search_start(
            case["seed"].as_str().expect("seed").parse().expect("u64"),
            case["generations"].as_u64().expect("generations") as u8,
            case["steps"].as_u64().expect("steps") as u8,
            case["hybrid"].as_bool().expect("arm"),
            (case["generations"].as_u64().expect("generations") + 1) * 8,
        );
        let mut state = execute(&package, &start).expect("initialize").output;
        for (index, reference) in expected.iter().enumerate() {
            if index != 0 {
                state = execute(&package, &search_input(b"ASST", &state))
                    .expect("search transition")
                    .output;
                transitions += 1;
            }
            let reference = unhex(reference.as_str().expect("wire"));
            assert!(
                search_matches(&state, &reference),
                "seed {}, hybrid {}, transition {index}",
                case["seed"],
                case["hybrid"]
            );
            // Prove the comparator notices changed counters, instructions and
            // numerical content instead of merely validating the wire shape.
            for offset in [13 * 8, 256 + 72, 256 + 8, 256 + 128, 1408] {
                let mut changed = reference.clone();
                if [13 * 8, 256 + 72].contains(&offset) {
                    changed[offset] ^= 1;
                } else {
                    let value =
                        f64::from_le_bytes(changed[offset..offset + 8].try_into().expect("float"));
                    changed[offset..offset + 8].copy_from_slice(&(value + 1.0).to_le_bytes());
                }
                assert!(
                    !search_matches(&changed, &reference),
                    "live comparator fault at {offset}"
                );
            }
        }
        assert_eq!(search_word(&state, 12), 2);
    }
    assert_eq!(transitions, 138);
}

#[cfg(feature = "solver")]
#[test]
fn composed_search_live_selection_and_fitting_faults_cannot_match_the_oracle() {
    let oracle = json(&repo().join("library/tests/fixtures/autoresearch-search/torch-pcg-v1.json"));
    let case = &oracle["cases"][1];
    assert_eq!(case["seed"], "42");
    assert_eq!(case["hybrid"], true);
    for (file, before, after) in [
        ("tool_search.sigil", "rounds = 3;", "rounds = 0;"),
        (
            "tool_population.sigil",
            "fitness.get(i) < fitness.get(best)",
            "fitness.get(i) > fitness.get(best)",
        ),
        ("tool_population.sigil", "j = j + 2;", "j = j + 8;"),
    ] {
        let fixture = Fixture::new();
        let path = fixture.root.join("src").join(file);
        let source = std::fs::read_to_string(&path).expect("application source");
        assert_eq!(source.matches(before).count(), 1, "unique live fault");
        std::fs::write(path, source.replacen(before, after, 1)).expect("owned mutant");
        let package = fixture.compile();
        let mut state = execute(&package, &search_start(42, 2, 20, true, 24))
            .expect("mutant initialization")
            .output;
        let mut detected = false;
        for reference in case["states"]
            .as_array()
            .expect("trajectory")
            .iter()
            .skip(1)
        {
            match execute(&package, &search_input(b"ASST", &state)) {
                Ok(result) => {
                    state = result.output;
                    if !search_matches(&state, &unhex(reference.as_str().expect("wire"))) {
                        detected = true;
                        break;
                    }
                }
                Err(sigil_runtime::ToolError::Trapped { message })
                    if message == "tool returned error (422)" =>
                {
                    detected = true;
                    break;
                }
                other => panic!("unrelated execution failure: {other:?}"),
            }
        }
        assert!(detected, "live policy fault must be detected: {before}");
    }
}

#[cfg(feature = "solver")]
#[test]
fn composed_search_maximum_generation_and_candidate_bounds_keep_runtime_limits() {
    let package = Fixture::new().compile();
    let mut state = execute(&package, &search_start(u64::MAX, 40, 0, true, 328))
        .expect("maximum generations")
        .output;
    let mut transitions = 0;
    while search_word(&state, 12) != 2 {
        state = execute(&package, &search_input(b"ASST", &state))
            .expect("bounded maximum search")
            .output;
        transitions += 1;
    }
    assert_eq!(transitions, 368);
    assert_eq!(search_word(&state, 19), 41);
    let mut maximum = execute(&package, &search_start(42, 1, 20, true, 16))
        .expect("maximum candidate base")
        .output;
    maximum[262] = 12;
    for index in 0..11 {
        maximum[328 + index * 4..332 + index * 4].copy_from_slice(&[0, 4, 3, 1]);
    }
    maximum[372..376].copy_from_slice(&[4, 14, 0, 0]);
    let request = search_input(b"ASST", &maximum);
    let valid =
        execute(&package, &request).expect("12 instructions times 20 steps times 3 fitting rounds");
    assert_eq!(search_word(&valid.output, 14), 1);
    for (cooperative, engine, memory) in [
        (1, 10_000_000, 16 * 1024 * 1024),
        (500_000, 1, 16 * 1024 * 1024),
        (500_000, 10_000_000, 1),
    ] {
        assert!(
            sigil_runtime::execute_ephemeral_with_budgets(
                &package.compilation.wasm_inner,
                &request,
                cooperative,
                engine,
                memory,
                &sigil_runtime::IoGrants::none()
            )
            .is_err()
        );
    }
}

#[cfg(feature = "solver")]
#[test]
fn composed_search_fresh_command_line_workflow_resumes_without_host_search_logic() {
    let result = Command::new("python3")
        .args([
            "-W",
            "error::ResourceWarning",
            "-m",
            "unittest",
            "discover",
            "-s",
            "library/tests",
            "-p",
            "test_autoresearch_search.py",
        ])
        .current_dir(repo())
        .env("SIGIL_INTEGRATION_CLI", env!("CARGO_BIN_EXE_sigil"))
        .output()
        .expect("fresh native search workflow");
    assert!(result.status.success(), "{result:?}");
    assert!(
        String::from_utf8_lossy(&result.stderr).contains("Ran 5 tests"),
        "native workflow must actually execute"
    );
    assert!(
        !String::from_utf8_lossy(&result.stderr).contains("skipped="),
        "the native workflow must not be skipped"
    );
}
#[cfg(feature = "solver")]
fn floats(bytes: &[u8]) -> Vec<f64> {
    bytes
        .as_chunks::<8>()
        .0
        .iter()
        .map(|b| f64::from_le_bytes(*b))
        .collect()
}
#[cfg(feature = "solver")]
fn observe(fixture: &Fixture) -> Vec<f64> {
    floats(
        &execute(&fixture.compile(), b"")
            .expect("probe passes")
            .output,
    )
}
#[cfg(feature = "solver")]
const TRANSACTIONS: &str = r#"
    let trial=optim::new_trial(3,1);let w=numeric::zeros(3,1);let g=numeric::zeros(3,1);
    let cell=numeric::new_scalar();
    w.data.set(0,1.0);w.data.set(1,0.0-1.0);w.data.set(2,0.25);
    g.data.set(0,9.0);g.data.set(1,0.0-2.0);g.data.set(2,0.0);
    let before=alloc(0);
    if optim::begin_sign(trial,w,g,0.5,0.0-1.0,1.0,cell)!=0 {return -1;}
    if w.data.get(0)!=1.0 || w.data.get(1)!=0.0-1.0 {return -2;}
    if trial.proposed.data.get(0)!=0.5 || trial.proposed.data.get(1)!=0.0-0.5 || trial.proposed.data.get(2)!=0.25 {return -3;}
    if optim::begin_sign(trial,w,g,0.5,0.0-1.0,1.0,cell)!=-400 {return -4;}
    if optim::rollback(trial)!=0 || trial.phase!=0 || w.data.get(0)!=1.0 {return -5;}
    if optim::rollback(trial)!=-400 || optim::commit_into(trial,w,cell)!=-400 {return -6;}
    if optim::begin_sign(trial,w,g,4.0,0.0-1.0,1.0,cell)!=0 {return -7;}
    if trial.proposed.data.get(0)!=0.0-1.0 || trial.proposed.data.get(1)!=1.0 {return -8;}
    w.data.set(2,0.5);
    if optim::commit_into(trial,w,cell)!=-409 || trial.phase!=1 || w.data.get(0)!=1.0 || w.data.get(2)!=0.5 {return -9;}
    w.data.set(2,0.25);
    if optim::commit_into(trial,w,cell)!=0 || trial.phase!=0 {return -10;}
    if w.data.get(0)!=0.0-1.0 || w.data.get(1)!=1.0 || w.data.get(2)!=0.25 {return -11;}
    if optim::commit_into(trial,w,cell)!=-400 {return -12;}
    if optim::begin_sign(trial,w,g,0.0,0.0-1.0,1.0,cell)!=0 || optim::commit_into(trial,w,cell)!=0 {return -13;}
    if alloc(0)!=before {return -14;}
    observations.push(1.0);
"#;

#[cfg(feature = "solver")]
#[test]
fn optim_sign_clipping_commit_conflict_and_rollback_preserve_state() {
    assert_eq!(observe(&Fixture::probe(TRANSACTIONS)), vec![1.0]);
    assert_eq!(
        observe(&Fixture::probe(
            r#"
        let trial=optim::new_trial(1,1);let w=numeric::zeros(1,1);let g=numeric::zeros(1,1);let c=numeric::new_scalar();
        g.data.set(0,1.0);
        if optim::begin_sign(trial,w,g,1.0,0.0,0.0,c)!=0 || trial.proposed.data.get(0)!=0.0 {return -1;}
        if optim::commit_into(trial,w,c)!=0 {return -2;}
        g.data.set(0,0.0 * (0.0-1.0));
        if optim::begin_sign(trial,w,g,1.0,0.0-1.0,1.0,c)!=0 || trial.proposed.data.get(0)!=0.0 {return -3;}
        observations.push(1.0);
    "#
        )),
        vec![1.0]
    );
}

#[cfg(feature = "solver")]
#[test]
fn optim_late_errors_aliases_and_invalid_shapes_are_transactional() {
    let setup = r#"
        let trial=optim::new_trial(2,1);let w=numeric::zeros(2,1);let g=numeric::zeros(2,1);let c=numeric::new_scalar();
        trial.original.data.set(0,11.0);trial.original.data.set(1,12.0);
        trial.proposed.data.set(0,21.0);trial.proposed.data.set(1,22.0);
        w.data.set(0,1.0);w.data.set(1,2.0);g.data.set(0,1.0);g.data.set(1,0.0-1.0);
        let mut huge=1.0;let mut k=0;while k<1023 {huge=huge*2.0;k=k+1;}
        let saved_w=w.data.buf;let saved_g=g.data.buf;let saved_p=trial.proposed.data.buf;
        let before=alloc(0);
    "#;
    let cases = [
        ("", "0.0-1.0,0.0,4.0", -422),
        ("", "1.0,4.0,0.0", -422),
        ("", "huge+huge,0.0,4.0", -422),
        ("", "1.0,0.0,huge+huge", -422),
        ("", "1.0,0.0,1.0", -422),
        ("g.data.set(1,huge+huge);", "1.0,0.0,4.0", -422),
        ("w.data.set(1,huge);", "huge,0.0-huge,huge", -422),
        ("g.rows=1;g.cols=2;", "1.0,0.0,4.0", -422),
        ("g.data.count=1;", "1.0,0.0,4.0", -400),
        ("trial.error=1;", "1.0,0.0,4.0", -400),
        ("w.data.buf=trial.original.data.buf;", "1.0,0.0,30.0", -400),
        ("g.data.buf=trial.proposed.data.buf;", "1.0,0.0,4.0", -400),
        (
            "trial.proposed.data.buf=trial.original.data.buf;",
            "1.0,0.0,4.0",
            -400,
        ),
    ];
    for (alter, arguments, code) in cases {
        let body = format!("{setup}{alter}
            let status=optim::begin_sign(trial,w,g,{arguments},c);
            w.data.buf=saved_w;g.data.buf=saved_g;trial.proposed.data.buf=saved_p;
            if status!={code} || trial.phase!=0 || alloc(0)!=before {{return -1;}}
            if trial.original.data.get(0)!=11.0 || trial.original.data.get(1)!=12.0 ||
               trial.proposed.data.get(0)!=21.0 || trial.proposed.data.get(1)!=22.0 || w.data.get(0)!=1.0 {{return -2;}}
            observations.push(1.0);");
        assert_eq!(
            observe(&Fixture::probe(&body)),
            vec![1.0],
            "{alter} {arguments}"
        );
    }
    assert_eq!(
        observe(&Fixture::probe(
            r#"
        let a=optim::new_trial(0,1);let b=optim::new_trial(4097,1);let c=numeric::new_scalar();
        let w=numeric::zeros(1,1);let g=numeric::zeros(1,1);
        if a.error!=-400 || b.error!=-413 {return -1;}
        if optim::begin_sign(a,w,g,1.0,0.0,1.0,c)!=-400 || optim::rollback(b)!=-413 {return -2;}
        observations.push(1.0);
    "#
        )),
        vec![1.0]
    );
}

#[cfg(feature = "solver")]
#[test]
fn optim_maximum_shape_reuses_storage_and_live_faults_are_detected() {
    assert_eq!(
        observe(&Fixture::probe(
            r#"
        let trial=optim::new_trial(64,64);let w=numeric::zeros(64,64);let g=numeric::zeros(64,64);let c=numeric::new_scalar();
        let mut i=0;while i<4096 {w.data.set(i,1.0);g.data.set(i,1.0);i=i+1;}
        let before=alloc(0);
        if optim::begin_sign(trial,w,g,0.25,0.0,2.0,c)!=0 || optim::commit_into(trial,w,c)!=0 {return -1;}
        i=0;while i<4096 {if w.data.get(i)!=0.75 {return -2;}else{} i=i+1;}
        if alloc(0)!=before {return -3;}else{} observations.push(1.0);
    "#
        )),
        vec![1.0]
    );
    for (needle, replacement) in [
        ("return value - step;", "return value + step;"),
        (
            "if value < low { value = low; }",
            "if value < low { value = high; }",
        ),
        (
            "if weights.data.get(i) != trial.original.data.get(i)",
            "if false",
        ),
        (
            "// Accepted weights never changed: rollback discards the pending proposal.\n    trial.phase = 0;",
            "// Live incorrect rollback phase.\n    trial.phase = 1;",
        ),
    ] {
        let mutant = Fixture::probe(TRANSACTIONS);
        mutant.mutate(true, needle, replacement);
        let result = execute(&mutant.compile(), b"");
        assert!(
            result.is_err() || floats(&result.expect("report").output) != vec![1.0],
            "live fault {needle}"
        );
    }
}

#[cfg(feature = "solver")]
fn reference() -> serde_json::Value {
    json(&repo().join("library/tests/fixtures/autoresearch-fit/torch-v1.json"))
}
#[cfg(feature = "solver")]
fn unhex(text: &str) -> Vec<u8> {
    text.as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|b| u8::from_str_radix(std::str::from_utf8(b).expect("hex"), 16).expect("byte"))
        .collect()
}
#[cfg(feature = "solver")]
fn agrees(actual: &[f64], expected: &[f64]) -> bool {
    actual.len() == expected.len()
        && actual.iter().zip(expected).all(|(a, b)| {
            a.is_finite() && b.is_finite() && (a - b).abs() <= 1e-10 + 1e-10 * b.abs()
        })
}
#[cfg(feature = "solver")]
fn report_matches(output: &[u8], case: &serde_json::Value) -> bool {
    let request = unhex(case["request_hex"].as_str().expect("request"));
    if output.len() != 840 + request.len() || output[840..] != request {
        return false;
    }
    let header: Vec<_> = output[..64]
        .as_chunks::<8>()
        .0
        .iter()
        .map(|b| i64::from_le_bytes(*b))
        .collect();
    let decisions: Vec<_> = output[264..312]
        .as_chunks::<8>()
        .0
        .iter()
        .map(|b| i64::from_le_bytes(*b))
        .collect();
    let numbers = [floats(&output[64..264]), floats(&output[312..840])].concat();
    header == serde_json::from_value::<Vec<i64>>(case["expected_header"].clone()).expect("header")
        && decisions
            == serde_json::from_value::<Vec<i64>>(case["decisions"].clone()).expect("decisions")
        && agrees(
            &numbers,
            &serde_json::from_value::<Vec<f64>>(case["expected_numbers"].clone()).expect("numbers"),
        )
}

#[cfg(feature = "solver")]
#[test]
fn autoresearch_fit_matches_torch_acceptance_rollback_gradients_and_replay() {
    let fixture = Fixture::new();
    let package = fixture.compile();
    let oracle = reference();
    let cases = oracle["cases"].as_array().expect("cases");
    assert_eq!(cases.len(), 58);
    let earlier = json(&repo().join("library/tests/fixtures/autoresearch-cpu/torch-v1.json"));
    for old in earlier["cases"].as_array().expect("earlier cases") {
        let name = format!("{}-fit-0", old["name"].as_str().expect("name"));
        let regression = cases
            .iter()
            .find(|case| case["name"] == name)
            .expect("every earlier case");
        assert_eq!(regression["candidate"], old["candidate"]);
        assert_eq!(regression["steps"], old["steps"]);
        assert_eq!(regression["rounds"], 0);
        let numbers: Vec<f64> =
            serde_json::from_value(regression["expected_numbers"].clone()).expect("numbers");
        let old_values: Vec<f64> =
            serde_json::from_value(old["expected"].clone()).expect("old numbers");
        assert!(
            agrees(&numbers[11..25], &old_values),
            "zero-round regression: {name}"
        );
    }
    let mut maximum_fuel = 0;
    let mut decisions = std::collections::BTreeSet::new();
    for case in cases {
        let request = case["request_hex"].as_str().expect("request");
        let result = execute(&package, request.as_bytes())
            .unwrap_or_else(|error| panic!("{}: {error:?}", case["name"]));
        maximum_fuel = maximum_fuel.max(result.fuel_consumed);
        assert!(
            report_matches(&result.output, case),
            "{}: native {:?}, expected {:?}",
            case["name"],
            floats(&result.output[64..264]),
            case["expected_numbers"]
        );
        assert_eq!(
            execute(&package, request.as_bytes())
                .expect("replay")
                .output,
            result.output
        );
        for choice in case["decisions"].as_array().expect("decisions") {
            decisions.insert(choice.as_i64().expect("choice"));
        }
    }
    assert_eq!(decisions, std::collections::BTreeSet::from([-1, 0, 1]));
    assert_eq!(cases.iter().filter(|c| c["rounds"] == 0).count(), 41);
    assert!(
        cases
            .iter()
            .any(|c| c["name"] == "growing-rate-cap-fit-6" && c["expected_header"][5] == 6)
    );
    assert!(
        cases
            .iter()
            .any(|c| c["rounds"] == 6 && c["expected_header"][7] == 1)
    );
    println!(
        "58 fitting cases, 91 numbers each: {} Wasm bytes; maximum {} cooperative fuel",
        package.compilation.wasm_inner.len(),
        maximum_fuel
    );
}

#[cfg(feature = "solver")]
#[test]
fn autoresearch_native_records_preserve_every_fitting_bit_and_refuse_schema_faults() {
    let fixture = Fixture::new();
    let package = fixture.compile();
    let oracle = reference();
    let fields = [
        ("header_le", 0, 64),
        ("summary_f64le", 64, 88),
        ("weights_f64le", 88, 152),
        ("accepted_f64le", 152, 264),
        ("decisions_le", 264, 312),
        ("trace_f64le", 312, 840),
    ];
    let mut max_fuel = 0;
    let mut max_bytes = 0;
    for case in oracle["cases"].as_array().expect("cases") {
        let text = case["request_hex"].as_str().expect("request");
        let binary = execute(&package, text.as_bytes())
            .expect("binary reference")
            .output;
        assert!(
            report_matches(&binary, case),
            "reference was executed, not assumed"
        );
        let mut request = unhex(text);
        request[4] = 2;
        let encoded: String = request.iter().map(|b| format!("{b:02x}")).collect();
        let result = execute(&package, encoded.as_bytes())
            .unwrap_or_else(|e| panic!("record {}: {e:?}", case["name"]));
        max_fuel = max_fuel.max(result.fuel_consumed);
        max_bytes = max_bytes.max(result.output.len());
        let record: serde_json::Value =
            serde_json::from_slice(&result.output).expect("native JSON");
        assert_eq!(record.as_object().expect("object").len(), 9);
        assert_eq!(record["format"], "sigil-autoresearch-fit-record-v1");
        assert_eq!(record["numeric"], "binary64le-hex-v1");
        assert_eq!(record["request_hex"], encoded);
        for (key, start, end) in fields {
            assert_eq!(
                unhex(record[key].as_str().expect("hex field")),
                binary[start..end],
                "{key}"
            );
        }
        assert_eq!(
            execute(&package, encoded.as_bytes())
                .expect("record replay")
                .output,
            result.output
        );
    }
    assert!(max_bytes <= 4096);
    println!(
        "58 exact-bit fitting records: {max_bytes} maximum bytes, {max_fuel} maximum cooperative fuel; {} Wasm bytes",
        package.compilation.wasm_inner.len()
    );
    // SC-P4: a valid but mislabeled result must not pass the record comparator.
    // Editing the application schema proves the consumer sees a real field,
    // rather than treating successful JSON parsing as correctness.
    let mutated = Fixture::new();
    let path = mutated.root.join("src/tool_records.sigil");
    let source = std::fs::read_to_string(&path).expect("schema source");
    assert_eq!(source.matches("\"weights_f64le\"").count(), 1);
    std::fs::write(
        path,
        source.replacen("\"weights_f64le\"", "\"wrong_weights\"", 1),
    )
    .expect("live mutation");
    let mut request = unhex(oracle["cases"][0]["request_hex"].as_str().expect("request"));
    request[4] = 2;
    let encoded: String = request.iter().map(|b| format!("{b:02x}")).collect();
    let result = execute(&mutated.compile(), encoded.as_bytes()).expect("well-formed mutant");
    let record: serde_json::Value = serde_json::from_slice(&result.output).expect("JSON");
    assert!(record.get("weights_f64le").is_none());
    assert!(record.get("wrong_weights").is_some());
}

#[cfg(feature = "solver")]
#[test]
fn autoresearch_fit_refuses_bad_requests_and_keeps_runtime_limits() {
    let fixture = Fixture::new();
    let package = fixture.compile();
    let oracle = reference();
    let case = &oracle["cases"][0];
    let original = unhex(case["request_hex"].as_str().expect("wire"));
    let mut malformed = vec![
        (original[..original.len() - 1].to_vec(), 422),
        (vec![0; 129], 413),
    ];
    let mut excess_work = unhex(
        oracle["cases"]
            .as_array()
            .expect("cases")
            .iter()
            .find(|case| case["name"] == "maximum-12x20-fit-3")
            .expect("maximum")["request_hex"]
            .as_str()
            .expect("request"),
    );
    excess_work[5] = 4;
    malformed.push((excess_work, 413));
    for (index, value) in [
        (0, 0),
        (4, 3),
        (5, 7),
        (6, 1),
        (7, 1),
        (8, 0),
        (12, 2),
        (13, 21),
        (14, 0),
        (14, 13),
        (15, 2),
        (80, 8),
        (81, 3),
        (82, 16),
    ] {
        let mut bytes = original.clone();
        bytes[index] = value;
        malformed.push((
            bytes,
            if [5, 13, 14].contains(&index) && value > 6 {
                413
            } else {
                422
            },
        ));
    }
    for value in [f64::NAN, f64::INFINITY, 4097.0, -4097.0] {
        let mut bytes = original.clone();
        bytes[16..24].copy_from_slice(&value.to_le_bytes());
        malformed.push((bytes, 422));
    }
    for (bytes, code) in malformed {
        let text = bytes.iter().map(|b| format!("{b:02x}")).collect::<String>();
        let result = execute(&package, text.as_bytes());
        assert!(
            matches!(&result,Err(sigil_runtime::ToolError::Trapped {message})
            if message==&format!("tool returned error ({code})")),
            "{result:?}: {text}"
        );
    }
    let request = case["request_hex"].as_str().expect("wire");
    for version in [1_u8, 2] {
        let mut raw = original.clone();
        raw[4] = version;
        let text = raw.iter().map(|b| format!("{b:02x}")).collect::<String>();
        assert!(
            execute(&package, text.as_bytes()).is_ok(),
            "canonical accept twin"
        );
        let mut invalid = text.clone().into_bytes();
        invalid[20] = b'z';
        for input in [
            b"z".to_vec(),
            b"AFIT".to_vec(),
            text.to_uppercase().into_bytes(),
            text.as_bytes()[..text.len() - 1].to_vec(),
            invalid,
        ] {
            search_refuses(execute(&package, &input), 422);
        }
    }
    for (cooperative, engine, memory) in [
        (1, 10_000_000, 16 * 1024 * 1024),
        (500_000, 1, 16 * 1024 * 1024),
        (500_000, 10_000_000, 1),
    ] {
        assert!(
            sigil_runtime::execute_ephemeral_with_budgets(
                &package.compilation.wasm_inner,
                request.as_bytes(),
                cooperative,
                engine,
                memory,
                &sigil_runtime::IoGrants::none()
            )
            .is_err()
        );
    }
    assert!(report_matches(
        &execute(&package, request.as_bytes())
            .expect("positive control")
            .output,
        case
    ));
}

#[cfg(feature = "solver")]
#[test]
fn autoresearch_fit_live_faults_cannot_pass_the_reference() {
    let oracle = reference();
    let cases = oracle["cases"].as_array().expect("cases");
    let case = cases
        .iter()
        .find(|c| c["name"] == "sgd-20-fit-3")
        .expect("accept/reject case");
    let request = case["request_hex"].as_str().expect("request");
    for (needle, replacement) in [
        ("let reset = autodiff::reset(tape);", "let reset = 0;"),
        (
            "if proposal_fitness < base_fitness {",
            "if proposal_fitness > base_fitness {",
        ),
        (
            "let committed = optim::commit_into(trial, weights, scalar);",
            "let committed = optim::rollback(trial);",
        ),
        (
            "let rolled_back = optim::rollback(trial);",
            "let rolled_back = optim::commit_into(trial, weights, scalar);",
        ),
        (
            "bytes::copy_into(output, 968, 152, accepted_result.data.buf, 112, 0, 112)",
            "bytes::copy_into(output, 968, 152, work.result.data.buf, 112, 0, 112)",
        ),
        (
            "let before = alloc(0);",
            "let before = alloc(0);let leaked=alloc(8);store8(leaked,1);",
        ),
    ] {
        let fixture = Fixture::new();
        fixture.mutate(false, needle, replacement);
        let result = execute(&fixture.compile(), request.as_bytes());
        match result {
            Ok(result) => assert!(
                !report_matches(&result.output, case),
                "live fault: {needle}"
            ),
            Err(sigil_runtime::ToolError::Trapped { .. }) => {}
            Err(error) => panic!("unexpected mutant failure: {error:?}"),
        }
    }
}

#[cfg(feature = "solver")]
#[test]
fn optim_public_only_labels_and_fresh_fitting_workflow_are_enforced() {
    for label in ["Public", "Internal", "Secret"] {
        let fixture = Fixture::new();
        std::fs::write(fixture.root.join("src/tool.sigil"),format!(
            "module tool;use sigil::optim;use sigil::numeric;
            fn sample(step:f64 @{label})->i64 @{label} ! {{Alloc}} {{
                let trial=optim::new_trial(1,1);let w=numeric::zeros(1,1);let g=numeric::zeros(1,1);let cell=numeric::new_scalar();
                return optim::begin_sign(trial,w,g,step,0.0,1.0,cell);}}
            pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return 0;}}"
        )).expect("label caller");
        fixture.lock();
        let result = Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["check", "--package"])
            .arg(&fixture.root)
            .arg("--json")
            .output()
            .expect("check");
        if label == "Public" {
            assert!(result.status.success(), "{result:?}");
        } else {
            assert!(!result.status.success());
            let json: serde_json::Value = serde_json::from_slice(&result.stdout).expect("JSON");
            let codes = json["diagnostics"]
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
    let result = Command::new("python3")
        .args([
            "-W",
            "error::ResourceWarning",
            "-m",
            "unittest",
            "discover",
            "-s",
            "library/tests",
            "-p",
            "test_autoresearch_fit.py",
        ])
        .current_dir(repo())
        .env("SIGIL_INTEGRATION_CLI", env!("CARGO_BIN_EXE_sigil"))
        .output()
        .expect("fresh workflow");
    assert!(result.status.success(), "{result:?}");
    assert!(
        !String::from_utf8_lossy(&result.stderr).contains("Ran 0 tests"),
        "workflow must actually execute"
    );
}
