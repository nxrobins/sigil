//! WHY THIS TEST EXISTS. Evaluation replies must match the whole expected request,
//! preserve classification and reject ambiguity before application state advances.
//! This tests message integrity and bounds, not worker honesty or authentication.
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
fn hash(raw: &[u8]) -> String {
    format!(
        "sha256:{}",
        ring::digest::digest(&ring::digest::SHA256, raw)
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
}
impl Fixture {
    fn dependency(&self, name: &str) -> LocalPackageDependency {
        LocalPackageDependency {
            package: format!("sigil/{name}"),
            path: self.directory.join(name),
        }
    }
    fn new() -> Self {
        let directory = loop {
            let path = std::env::temp_dir().join(format!(
                "sigil-exchange-{}-{}",
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
        std::fs::create_dir_all(root.join("src")).expect("root");
        let fixture = Self { directory, root };
        let names = ["json", "records", "exchange"];
        let mut deps = Vec::new();
        for (index, name) in names.iter().enumerate() {
            copy(
                &repo().join("library/packages").join(name),
                &fixture.directory.join(name),
            );
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
            deps.push(serde_json::json!({"package":format!("sigil/{name}"),"requirement":"=0.1.0-public.1","source":"workspace","content_hash":pin,"features":[],"default_features":false,"optional":false}));
        }
        deps.sort_by_key(|d| d["package"].as_str().expect("name").to_string());
        let mut manifest = json(&repo().join("library/programs/autoresearch/sigil-package.json"));
        manifest["namespace"] = "exchange-probe".into();
        manifest["modules"] = serde_json::json!(["tool"]);
        manifest["dependencies"] = deps.into();
        manifest["declared"]["taint_contracts"] =
            serde_json::json!(["tool::tool_main(input_ptr:Public,input_len:Public)->Public"]);
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
            &["json", "records", "exchange"].map(|n| self.dependency(n)),
        )
        .expect("root graph")
    }
    #[cfg(feature = "solver")]
    fn probe(body: &str) -> Self {
        let fixture = Self::new();
        std::fs::write(fixture.root.join("src/tool.sigil"),format!("module tool;use sigil::exchange;pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{{body}}}")).expect("probe");
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
        .expect("solver graph")
    }
    #[cfg(feature = "solver")]
    fn mutate(&self, needle: &str, replacement: &str) {
        let old_root = self.root.join("sigil-package.lock.json");
        std::fs::rename(&old_root, old_root.with_extension("before")).expect("preserve root lock");
        let path = self.directory.join("exchange/src/exchange.sigil");
        let source = std::fs::read_to_string(&path).expect("source");
        assert_eq!(source.matches(needle).count(), 1);
        std::fs::write(path, source.replacen(needle, replacement, 1)).expect("owned mutant");
        let prior = self.directory.join("exchange/sigil-package.lock.json");
        std::fs::rename(&prior, prior.with_extension("before")).expect("preserve own lock");
        let graph: serde_json::Value = serde_json::from_slice(
            &create_local_package_lock_with_dependencies(
                &self.directory.join("exchange"),
                &[self.dependency("json"), self.dependency("records")],
            )
            .expect("mutant graph"),
        )
        .expect("graph");
        let pin = graph["nodes"]
            .as_array()
            .expect("nodes")
            .iter()
            .find(|n| n["package"] == "sigil/exchange")
            .expect("provider")["content_hash"]
            .clone();
        let path = self.root.join("sigil-package.json");
        let mut manifest = json(&path);
        manifest["dependencies"]
            .as_array_mut()
            .expect("deps")
            .iter_mut()
            .find(|d| d["package"] == "sigil/exchange")
            .expect("pin")["content_hash"] = pin;
        std::fs::write(path, serde_json::to_vec(&manifest).expect("encode")).expect("repin");
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

#[test]
fn exchange_metadata_and_fresh_graph_bind_every_input() {
    let root = repo().join("library/packages/exchange");
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
    for (file, pin) in json(&root.join("inputs.json"))["files"]
        .as_object()
        .expect("inventory")
    {
        let mut raw = std::fs::read(root.join(file)).expect("input");
        assert_eq!(pin, &hash(&raw));
        raw.push(0);
        assert_ne!(pin, &hash(&raw));
    }
    let fixture = Fixture::new();
    let graph: serde_json::Value = serde_json::from_slice(&fixture.lock()).expect("graph");
    assert_eq!(graph["nodes"].as_array().expect("nodes").len(), 4);
}
#[cfg(feature = "solver")]
fn execute(
    p: &sigil_compiler::package::PackageCompilation,
    input: &[u8],
) -> Result<sigil_runtime::ToolResult, sigil_runtime::ToolError> {
    sigil_runtime::execute_ephemeral_with_budgets(
        &p.compilation.wasm_inner,
        input,
        500_000,
        10_000_000,
        16 * 1024 * 1024,
        &sigil_runtime::IoGrants::none(),
    )
}
#[cfg(feature = "solver")]
fn refused(result: Result<sigil_runtime::ToolResult, sigil_runtime::ToolError>, code: u16) {
    assert!(
        matches!(&result,Err(sigil_runtime::ToolError::Trapped{message}) if message==&format!("tool returned error ({code})")),
        "{result:?}"
    );
}
#[cfg(feature = "solver")]
fn hex(raw: &[u8]) -> String {
    raw.iter().map(|b| format!("{b:02x}")).collect()
}
#[cfg(feature = "solver")]
fn request(profile: &str, context: &[u8], sequence: u64, payload: &[u8]) -> Vec<u8> {
    format!("{{\"format\":\"sigil-evaluation-request-v1\",\"profile\":\"{profile}\",\"context_hex\":\"{}\",\"sequence\":\"{sequence:016x}\",\"payload_hex\":\"{}\"}}",hex(context),hex(payload)).into_bytes()
}
#[cfg(feature = "solver")]
fn response(req: &[u8], status: u64, payload: &[u8]) -> Vec<u8> {
    format!("{{\"format\":\"sigil-evaluation-response-v1\",\"request_hex\":\"{}\",\"status\":\"{status:016x}\",\"payload_hex\":\"{}\"}}",hex(req),hex(payload)).into_bytes()
}
#[cfg(feature = "solver")]
fn joined(a: &[u8], b: &[u8]) -> Vec<u8> {
    [a, b"\n", b].concat()
}
#[cfg(feature = "solver")]
const SPLIT: &str = "let mut n=0;while n<input_len && load8(input_ptr+n)!=10 {n=n+1;}if n==input_len {return -400;}";
#[cfg(feature = "solver")]
const READ: &str = "let r=exchange::open_request(input_ptr,input_len);if r.error<0 {return r.error;}return r.payload*4294967296+r.payload_len;";
#[cfg(feature = "solver")]
const RECEIVE: &str = "let r=exchange::open_response(input_ptr,n,input_ptr+n+1,input_len-n-1);if r.error<0 {return r.error;}return r.payload*4294967296+r.payload_len;";

#[cfg(feature = "solver")]
#[test]
fn exchange_round_trips_maximum_messages_statuses_and_exact_identity() {
    let make=Fixture::probe("let p=alloc(64);let c=alloc(128);let mut i=0;while i<128 {store8(c+i,i);if i<64 {store8(p+i,120);}else{}i=i+1;}let high:u64=4294967295;let seq:u64=high*4294967296+high;return exchange::request(p,64,c,128,seq,input_ptr,input_len);").compile();
    let read = Fixture::probe(READ).compile();
    let receive = Fixture::probe(&(SPLIT.to_owned() + RECEIVE)).compile();
    let context = (0..128).collect::<Vec<u8>>();
    let raw = (0..=255).cycle().take(512).collect::<Vec<u8>>();
    for payload in [b"".as_slice(), raw.as_slice()] {
        let req = execute(&make, payload).expect("request").output;
        assert_eq!(req, request(&"x".repeat(64), &context, u64::MAX, payload));
        assert_eq!(execute(&read, &req).expect("read").output, payload);
        for status in 0..=4 {
            let sender = Fixture::probe(&format!(
                "{SPLIT}return exchange::respond(input_ptr,n,{status},input_ptr+n+1,input_len-n-1);"
            ))
            .compile();
            let body = vec![0xa5; 1024];
            let reply = execute(&sender, &joined(&req, &body)).expect("response");
            assert_eq!(reply.output, response(&req, status, &body));
            let result = execute(&receive, &joined(&req, &reply.output)).expect("receive maximum");
            assert_eq!(result.output, body);
            println!(
                "exchange request={} response={} receive fuel={}",
                req.len(),
                reply.output.len(),
                result.fuel_consumed
            );
            refused(execute(&sender, &joined(&req, &vec![0; 1025])), 413);
        }
    }
    refused(execute(&make, &vec![0; 513]), 413);
}

#[cfg(feature = "solver")]
#[test]
fn exchange_refuses_noncanonical_bounds_and_every_request_mismatch() {
    let reader = Fixture::probe(READ).compile();
    let receiver = Fixture::probe(&(SPLIT.to_owned() + RECEIVE)).compile();
    let req = request("fit-v1", b"job", 7, b"candidate");
    let reply = response(&req, 0, b"answer");
    assert_eq!(
        execute(&receiver, &joined(&req, &reply))
            .expect("accept twin")
            .output,
        b"answer"
    );
    for different in [
        request("fit-v2", b"job", 7, b"candidate"),
        request("fit-v1", b"other", 7, b"candidate"),
        request("fit-v1", b"job", 8, b"candidate"),
        request("fit-v1", b"job", 7, b"changed"),
    ] {
        refused(execute(&receiver, &joined(&different, &reply)), 409);
    }
    let text = String::from_utf8(req.clone()).expect("JSON");
    for bad in [
        format!(" {text}"),
        text.replacen("{", "{\"extra\":0,", 1),
        text.replacen("{", "{\"profile\":\"fit-v1\",", 1),
        text.replace("fit-v1", "FIT-v1"),
        text.replace("0000000000000007", "000000000000000G"),
    ] {
        refused(execute(&reader, bad.as_bytes()), 422);
    }
    refused(execute(&reader, b"{"), 400);
    refused(execute(&reader, b"{}"), 404);
    refused(execute(&reader, &vec![32; 1537]), 413);
    refused(execute(&reader, &request("", b"job", 0, b"")), 422);
    refused(execute(&reader, &request("a", b"", 0, b"")), 422);
    refused(
        execute(&reader, &request(&"x".repeat(65), b"j", 0, b"")),
        413,
    );
    refused(execute(&reader, &request("a", &[0; 129], 0, b"")), 413);
    let text = String::from_utf8(reply.clone()).expect("JSON");
    for bad in [
        format!(" {text}"),
        text.replacen("{", "{\"extra\":0,", 1),
        text.replacen("{", "{\"status\":\"0000000000000000\",", 1),
    ] {
        refused(execute(&receiver, &joined(&req, bad.as_bytes())), 422);
    }
    refused(
        execute(&receiver, &joined(&req, &response(&req, 5, b""))),
        422,
    );
    refused(
        execute(&receiver, &joined(&req, &response(&req, 0, &[0; 1025]))),
        413,
    );
    refused(execute(&receiver, &joined(&req, &vec![32; 6145])), 413);
}

#[cfg(feature = "solver")]
#[test]
fn exchange_live_matching_and_canonicality_faults_are_detected() {
    let req = request("fit-v1", b"job", 7, b"candidate");
    let text = String::from_utf8(req.clone()).expect("JSON");
    let duplicate = text.replacen("{", "{\"extra\":0,", 1);
    let fixture = Fixture::probe(READ);
    refused(execute(&fixture.compile(), duplicate.as_bytes()), 422);
    fixture.mutate("if !equal(ptr, len, canonical / 4294967296, canonical % 4294967296) { return failed_request(-422); } else {}","if false { return failed_request(-422); } else {}");
    assert_eq!(
        execute(&fixture.compile(), duplicate.as_bytes())
            .expect("fault observed")
            .output,
        b"candidate"
    );
    // A canonical response with another request is independently refused at both
    // exact matching and canonical reconstruction. Kill either fence only after
    // using a witness that reaches the other, rather than calling redundancy dead.
    let fixture = Fixture::probe(&(SPLIT.to_owned() + RECEIVE));
    let different = request("fit-v1", b"other", 7, b"candidate");
    let input = joined(&req, &response(&different, 0, b"answer"));
    refused(execute(&fixture.compile(), &input), 409);
    fixture.mutate("if !equal(expected_ptr, expected_len, actual / 4294967296, actual % 4294967296) { return failed_reply(-409); } else {}","if false { return failed_reply(-409); } else {}");
    refused(execute(&fixture.compile(), &input), 422);
}

#[cfg(feature = "solver")]
#[test]
fn exchange_decoding_and_refusals_preserve_prior_bytes() {
    let body = "let saved=alloc(input_len);let mut i=0;while i<input_len {store8(saved+i,load8(input_ptr+i));i=i+1;}
        let r=exchange::open_request(input_ptr,input_len);if r.error<0 {return r.error;}
        if r.payload_len>0 {store8(r.payload,33);}else{}
        let failed=exchange::respond(input_ptr,input_len,5,0,0);if failed != -422 {return -500;}
        i=0;while i<input_len {if load8(saved+i)!=load8(input_ptr+i) {return -500;}else{}i=i+1;}
        return r.payload*4294967296+r.payload_len;";
    let fixture = Fixture::probe(body);
    let req = request("fit-v1", b"job", 7, b"candidate");
    assert_eq!(
        execute(&fixture.compile(), &req)
            .expect("fresh decoded storage")
            .output,
        b"!andidate"
    );
    fixture.mutate(
        "\n        payload: payload / 4294967296, payload_len: payload % 4294967296, error: 0 };",
        "\n        payload: ptr, payload_len: payload % 4294967296, error: 0 };",
    );
    refused(execute(&fixture.compile(), &req), 500);
}

#[cfg(feature = "solver")]
#[test]
fn exchange_labels_and_independent_resource_limits_remain_enforced() {
    for (label, result, passes) in [
        ("Public", "Public", true),
        ("Internal", "Internal", true),
        ("Secret", "Secret", true),
        ("Internal", "Public", false),
        ("Secret", "Internal", false),
    ] {
        let fixture = Fixture::new();
        std::fs::write(fixture.root.join("src/tool.sigil"),format!("module tool;use sigil::exchange;fn encoded(ptr:i64 @{label},len:i64 @{label})->i64 @{result} ! {{Alloc}} {{let r:EvaluationRequest @{label}=exchange::open_request(ptr,len);return r.payload;}} pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return 0;}}")).expect("label probe");
        fixture.lock();
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_sigil"))
            .args(["check", "--package"])
            .arg(&fixture.root)
            .arg("--json")
            .output()
            .expect("check");
        assert_eq!(output.status.success(), passes, "{output:?}");
        if !passes {
            let body: serde_json::Value = serde_json::from_slice(&output.stdout).expect("envelope");
            let codes = body["diagnostics"]
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
    let p = Fixture::probe(READ).compile();
    let req = request("fit-v1", b"job", 7, b"candidate");
    assert_eq!(execute(&p, &req).expect("control").output, b"candidate");
    for (fuel, engine, memory) in [
        (1, 10_000_000, 16 * 1024 * 1024),
        (500_000, 1, 16 * 1024 * 1024),
        (500_000, 10_000_000, 1),
    ] {
        assert!(
            sigil_runtime::execute_ephemeral_with_budgets(
                &p.compilation.wasm_inner,
                &req,
                fuel,
                engine,
                memory,
                &sigil_runtime::IoGrants::none()
            )
            .is_err()
        );
    }
}
