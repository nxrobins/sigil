//! WHY THIS TEST EXISTS. Checkpoints need exact numeric bits, whole-document
//! validation and persistent prior state, not lossy host-side JSON assembly.
//! Exercise the packaged existing codec, immutable construction and live faults.
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
        let kind = entry.file_type().expect("type");
        if kind.is_dir() {
            copy(&entry.path(), &target.join(entry.file_name()));
        } else {
            assert!(kind.is_file());
            std::fs::copy(entry.path(), target.join(entry.file_name())).expect("copy");
        }
    }
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
}
impl Fixture {
    fn new() -> Self {
        let directory = loop {
            let path = std::env::temp_dir().join(format!(
                "sigil-records-{}-{}",
                std::process::id(),
                SEQUENCE.fetch_add(1, Ordering::Relaxed)
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => break path,
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("owned directory: {e}"),
            }
        };
        let root = directory.join("consumer");
        std::fs::create_dir_all(root.join("src")).expect("root");
        for name in ["records", "json"] {
            copy(
                &repo().join("library/packages").join(name),
                &directory.join(name),
            );
        }
        let codec =
            json(&repo().join("library/packages/records/sigil-package.json"))["dependencies"][0]
                .clone();
        let graph: serde_json::Value = serde_json::from_slice(
            &create_local_package_lock_with_dependencies(
                &directory.join("records"),
                &[LocalPackageDependency {
                    package: "sigil/json".into(),
                    path: directory.join("json"),
                }],
            )
            .expect("provider graph"),
        )
        .expect("graph");
        let pin = graph["nodes"]
            .as_array()
            .expect("nodes")
            .iter()
            .find(|n| n["package"] == "sigil/records")
            .expect("records")["content_hash"]
            .clone();
        let mut manifest = json(&repo().join("library/programs/autoresearch/sigil-package.json"));
        manifest["namespace"] = "record-probe".into();
        manifest["modules"] = serde_json::json!(["tool"]);
        manifest["declared"]["taint_contracts"] =
            serde_json::json!(["tool::tool_main(input_ptr:Public,input_len:Public)->Public"]);
        manifest["dependencies"] = serde_json::json!([codec,
            {"package":"sigil/records","requirement":"=0.1.0-public.1","source":"workspace","content_hash":pin,
             "features":[],"default_features":false,"optional":false}]);
        std::fs::write(
            root.join("sigil-package.json"),
            serde_json::to_vec(&manifest).expect("manifest"),
        )
        .expect("write");
        std::fs::write(root.join("src/tool.sigil"),"module tool;pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {Alloc} {let p=alloc(1);store8(p,65);return p*4294967296+1;}").expect("tool");
        Self { directory, root }
    }
    fn lock(&self) -> Vec<u8> {
        create_local_package_lock_with_dependencies(
            &self.root,
            &["records", "json"].map(|name| LocalPackageDependency {
                package: format!("sigil/{name}"),
                path: self.directory.join(name),
            }),
        )
        .expect("graph")
    }
    #[cfg(feature = "solver")]
    fn probe(body: &str) -> Self {
        let fixture = Self::new();
        std::fs::write(fixture.root.join("src/tool.sigil"),format!(
            "module tool;use sigil::records;pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{{body}}}"
        )).expect("probe");
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
        let path = self.directory.join("records/src/records.sigil");
        let source = std::fs::read_to_string(&path).expect("source");
        assert_eq!(source.matches(needle).count(), 1);
        std::fs::write(path, source.replacen(needle, replacement, 1)).expect("mutant");
        let saved = self.directory.join("records/sigil-package.lock.json");
        std::fs::rename(&saved, saved.with_extension("before")).expect("preserve own lock");
        let graph: serde_json::Value = serde_json::from_slice(
            &create_local_package_lock_with_dependencies(
                &self.directory.join("records"),
                &[LocalPackageDependency {
                    package: "sigil/json".into(),
                    path: self.directory.join("json"),
                }],
            )
            .expect("new identity"),
        )
        .expect("graph");
        let identity = graph["nodes"]
            .as_array()
            .expect("nodes")
            .iter()
            .find(|n| n["package"] == "sigil/records")
            .expect("records")["content_hash"]
            .clone();
        let mut manifest = json(&self.root.join("sigil-package.json"));
        manifest["dependencies"][1]["content_hash"] = identity;
        std::fs::write(
            self.root.join("sigil-package.json"),
            serde_json::to_vec(&manifest).expect("encode"),
        )
        .expect("repin owned mutant");
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}

#[test]
fn records_metadata_codec_bytes_and_locked_drift_are_checked() {
    let original = std::fs::read(repo().join("stdlib/sigil/json.sigil")).expect("original codec");
    let mut packaged =
        std::fs::read(repo().join("library/packages/json/src/json.sigil")).expect("packaged codec");
    assert_eq!(original, packaged);
    packaged.push(b'!');
    assert_ne!(original, packaged, "live drift detector");
    for name in ["records", "json"] {
        let root = repo().join("library/packages").join(name);
        let manifest = json(&root.join("sigil-package.json"));
        assert_eq!(
            manifest["version"],
            json(&root.join("api-card.json"))["version"]
        );
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
            .expect("inputs")
        {
            let mut bytes = std::fs::read(root.join(file)).expect("file");
            assert_eq!(expected, &hash(&bytes));
            bytes.push(b'!');
            assert_ne!(expected, &hash(&bytes));
        }
    }
    let fixture = Fixture::new();
    let locked = fixture.lock();
    let graph: serde_json::Value = serde_json::from_slice(&locked).expect("graph");
    assert_eq!(graph["nodes"].as_array().expect("nodes").len(), 3);
    let provider = graph["nodes"]
        .as_array()
        .expect("nodes")
        .iter()
        .find(|n| n["package"] == "sigil/records")
        .expect("records");
    let cached = fixture
        .root
        .join(provider["source"]["locator"].as_str().expect("cache"));
    std::fs::write(cached.join("src/records.sigil"), "module records;\n").expect("drift");
    let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
        .args(["check", "--package"])
        .arg(&fixture.root)
        .arg("--json")
        .output()
        .expect("check");
    assert!(!output.status.success());
    let body: serde_json::Value = serde_json::from_slice(&output.stdout).expect("envelope");
    assert_eq!(body["data"]["code"], "E_HASH_MISMATCH");
    assert_eq!(
        std::fs::read(fixture.root.join("sigil-package.lock.json")).expect("lock"),
        locked
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
fn text_literal(name: &str, bytes: &[u8]) -> String {
    let mut out = format!("let {name}=alloc({});", bytes.len());
    for (index, byte) in bytes.iter().enumerate() {
        out.push_str(&format!("store8({name}+{index},{byte});"));
    }
    out
}
#[cfg(feature = "solver")]
fn refused(result: Result<sigil_runtime::ToolResult, sigil_runtime::ToolError>, code: i64) {
    assert!(
        matches!(&result,Err(sigil_runtime::ToolError::Trapped{message}) if message==&format!("tool returned error ({code})")),
        "{result:?}"
    );
}

#[cfg(feature = "solver")]
#[test]
fn records_build_nested_json_escape_controls_and_keep_prior_objects() {
    for value in [
        b"null".as_slice(),
        b"true",
        b"-1.25e+30",
        br#"[1,{"nested":"\u03bb"}]"#,
    ] {
        let body=format!("{} let empty=records::new(32768);let next=records::put_json(empty,key,1,input_ptr,input_len);
            if empty.length!=2 || empty.fields!=0 || load8(empty.ptr+1)!=125 {{return -1;}}
            return records::finish(next);",text_literal("key",b"v"));
        let fixture = Fixture::probe(&body);
        let package = fixture.compile();
        let result = execute(&package, value).expect("object");
        let parsed: serde_json::Value =
            serde_json::from_slice(&result.output).expect("real JSON consumer");
        assert_eq!(
            parsed,
            serde_json::json!({"v":serde_json::from_slice::<serde_json::Value>(value).expect("reference")})
        );
    }
    let body = format!(
        "{}let old=records::new(32768);let next=records::put_string(old,key,4,input_ptr,input_len);return records::finish(next);",
        text_literal("key", b"text")
    );
    let fixture = Fixture::probe(&body);
    let package = fixture.compile();
    let input = (0..128).collect::<Vec<u8>>();
    let output = execute(&package, &input).expect("ASCII controls").output;
    let decoded: serde_json::Value = serde_json::from_slice(&output).expect("valid escaped JSON");
    assert_eq!(decoded["text"].as_str().expect("string").as_bytes(), input);
    refused(execute(&package, &[0xc3, 0xa9]), 422);
    let large = vec![0; 2048];
    assert!(execute(&package, &large).is_ok());
    refused(execute(&package, &vec![0; 2049]), 413);
}

#[cfg(feature = "solver")]
#[test]
fn records_refusals_preserve_previous_bytes_and_propagate_errors() {
    let body=format!("{}let empty=records::new(128);let first=records::put_json(empty,key,1,input_ptr,input_len);
        if first.error<0 {{return first.error;}}
        let before=first.length;let repeated=records::put_json(first,key,1,input_ptr,input_len);
        if repeated.error!=-409 || records::finish(repeated)!=-409 {{return -1;}}
        let again=records::put_string(repeated,key,1,input_ptr,input_len);if again.error!=-409 {{return -2;}}
        let numeric=records::put_f64le(repeated,key,1,input_ptr,-1);if numeric.error!=-409 {{return -4;}}
        if first.length!=before || first.fields!=1 || empty.length!=2 {{return -3;}}
        return records::finish(first);",text_literal("key",b"v"));
    let fixture = Fixture::probe(&body);
    let package = fixture.compile();
    assert_eq!(
        execute(&package, b"123").expect("preserved").output,
        b"{\"v\":123}"
    );
    for invalid in [
        b"".as_slice(),
        b"01",
        b"{} trailing",
        b"[1,]",
        b"{\"a\":1",
        b"NaN",
    ] {
        refused(execute(&package, invalid), 400);
    }
    let body=format!("{}let empty=records::new(7);let next=records::put_json(empty,key,1,input_ptr,input_len);
        if next.error!=-413 || empty.length!=2 || load8(empty.ptr)!=123 || load8(empty.ptr+1)!=125 {{return -1;}}
        return records::finish(empty);",text_literal("key",b"x"));
    assert_eq!(
        execute(&Fixture::probe(&body).compile(), b"12")
            .expect("unchanged empty")
            .output,
        b"{}"
    );
    let body = format!(
        "{}let doc=records::new(32768);let result=records::put_json(doc,input_ptr,input_len,value,1);return records::finish(result);",
        text_literal("value", b"0")
    );
    let fixture = Fixture::probe(&body);
    let package = fixture.compile();
    for (key, code) in [
        (b"".as_slice(), 400),
        (b"1x", 422),
        (b"a\"b", 422),
        (b"UPPER", 422),
    ] {
        refused(execute(&package, key), code);
    }
    assert!(execute(&package, &[b'a'; 64]).is_ok());
    refused(execute(&package, &[b'a'; 65]), 413);
    let field = format!(
        "{}return records::field(input_ptr,input_len,key,1);",
        text_literal("key", b"a")
    );
    let package = Fixture::probe(&field).compile();
    assert_eq!(execute(&package, b"{\"a\":1}").expect("field").output, b"1");
    for invalid in [
        b"{\"a\":1".as_slice(),
        b"{\"a\":1}garbage",
        b"{\"a\":1,\"b\":01}",
    ] {
        refused(execute(&package, invalid), 400);
    }
    refused(execute(&package, b"{}"), 404);
    let capacity = format!(
        "{}let doc=records::new(8);let next=records::put_json(doc,key,1,input_ptr,input_len);return records::finish(next);",
        text_literal("key", b"x")
    );
    let package = Fixture::probe(&capacity).compile();
    assert_eq!(
        execute(&package, b"12").expect("exact capacity").output,
        b"{\"x\":12}"
    );
    refused(execute(&package, b"123"), 413);
    let fields = format!("{}let key=alloc(3);store8(key,107);let mut doc=records::new(1024);let mut i=0;
        while i<32 {{store8(key+1,97+i/26);store8(key+2,97+i%26);
            let next=records::put_json(doc,key,3,value,1);if next.error<0 {{return next.error;}}doc=next;i=i+1;}}
        store8(key+1,122);store8(key+2,122);let excess=records::put_json(doc,key,3,value,1);
        if excess.error!=-413 || doc.fields!=32 {{return -1;}}return records::finish(doc);",text_literal("value",b"0"));
    let result = execute(&Fixture::probe(&fields).compile(), b"").expect("field boundary");
    let object: serde_json::Value = serde_json::from_slice(&result.output).expect("preserved JSON");
    assert_eq!(object.as_object().expect("object").len(), 32);
    assert!(
        object
            .as_object()
            .expect("object")
            .values()
            .all(|value| value == 0)
    );
}

#[cfg(feature = "solver")]
#[test]
fn records_exact_words_floats_and_blobs_round_trip_without_loss() {
    for value in [0_u64, 1, 1 << 53, 1 << 63, u64::MAX] {
        let body=format!("{}let high:u64={};let value:u64=high*4294967296+{};
            let doc=records::new(64);let next=records::put_u64(doc,key,1,value);return records::finish(next);",
            text_literal("key",b"v"),value>>32,value&0xffff_ffff);
        let fixture = Fixture::probe(&body);
        let output = execute(&fixture.compile(), b"").expect("word").output;
        let decoded: serde_json::Value = serde_json::from_slice(&output).expect("JSON");
        assert_eq!(decoded["v"], format!("{value:016x}"));
        let read=format!("let word=records::read_u64(input_ptr,input_len);if word.error<0 {{return word.error;}}
            {}let doc=records::new(64);let next=records::put_u64(doc,key,1,word.value);return records::finish(next);",text_literal("key",b"v"));
        assert_eq!(
            execute(
                &Fixture::probe(&read).compile(),
                format!("{value:016x}").as_bytes()
            )
            .expect("read word")
            .output,
            output
        );
    }
    let body = format!(
        "{}let doc=records::new(16384);let next=records::put_f64le(doc,key,1,input_ptr,input_len/8);return records::finish(next);",
        text_literal("key", b"v")
    );
    let fixture = Fixture::probe(&body);
    let package = fixture.compile();
    let values = [
        0.0_f64,
        -0.0,
        f64::from_bits(1),
        f64::MIN_POSITIVE,
        f64::MAX,
        -f64::MAX,
        1.0 / 3.0,
    ];
    let bytes = values
        .iter()
        .flat_map(|n| n.to_le_bytes())
        .collect::<Vec<_>>();
    let output = execute(&package, &bytes).expect("finite values").output;
    let doc: serde_json::Value = serde_json::from_slice(&output).expect("JSON");
    assert_eq!(
        doc["v"],
        bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()
    );
    let reader =
        Fixture::probe("return records::read_f64le(input_ptr,input_len,input_len/16);").compile();
    assert_eq!(
        execute(&reader, doc["v"].as_str().expect("hex").as_bytes())
            .expect("float decode")
            .output,
        bytes
    );
    for bits in [
        0x7ff0000000000000_u64,
        0xfff0000000000000,
        0x7ff0000000000001,
        0x7fffffffffffffff,
        0xfff8000000000000,
    ] {
        refused(execute(&package, &bits.to_le_bytes()), 422);
        let encoded = bits
            .to_le_bytes()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect::<String>();
        refused(execute(&reader, encoded.as_bytes()), 422);
    }
    let blob = Fixture::probe("return records::hex(input_ptr,input_len);").compile();
    let raw = (0..=255).cycle().take(1024).collect::<Vec<u8>>();
    let encoded = execute(&blob, &raw).expect("hex").output;
    let text: String = serde_json::from_slice(&encoded).expect("JSON string");
    let decoder = Fixture::probe("return records::unhex(input_ptr,input_len,8191);").compile();
    assert_eq!(
        execute(&decoder, text.as_bytes()).expect("decode").output,
        raw
    );
    for bad in [b"A0".as_slice(), b"0", b"zz", b"00 0"] {
        refused(execute(&decoder, bad), 422);
    }
    let word =
        Fixture::probe("let result=records::read_u64(input_ptr,input_len);return result.error;")
            .compile();
    refused(execute(&word, b"fffffffffffffff"), 422);
    refused(execute(&word, b"FFFFFFFFFFFFFFFF"), 422);
    let maximum = vec![0_u8; 512 * 8];
    let result = execute(&package, &maximum).expect("maximum finite array");
    let encoded: serde_json::Value = serde_json::from_slice(&result.output).expect("JSON");
    assert_eq!(
        execute(&reader, encoded["v"].as_str().expect("hex").as_bytes())
            .expect("maximum decode")
            .output,
        maximum
    );
    refused(execute(&package, &vec![0; 513 * 8]), 413);
    let raw = vec![0xa5; 8191];
    let output = execute(&blob, &raw).expect("maximum blob");
    let encoded: String = serde_json::from_slice(&output.output).expect("string");
    assert_eq!(
        execute(&decoder, encoded.as_bytes())
            .expect("maximum blob decode")
            .output,
        raw
    );
    refused(execute(&blob, &vec![0; 8192]), 413);
}

#[cfg(feature = "solver")]
#[test]
fn records_labels_cannot_lower_classification_and_runtime_limits_stay_enforced() {
    for (label, result, passes) in [
        ("Public", "Public", true),
        ("Internal", "Internal", true),
        ("Secret", "Secret", true),
        ("Internal", "Public", false),
        ("Secret", "Internal", false),
    ] {
        let fixture = Fixture::new();
        std::fs::write(fixture.root.join("src/tool.sigil"),format!(
            "module tool;use sigil::records;
            fn encoded(ptr:i64 @{label},len:i64 @{label})->i64 @{result} ! {{Alloc}} {{
                let key=alloc(1);store8(key,118);
                let empty:JsonRecord @{label}=records::new(256);
                let next:JsonRecord @{label}=records::put_hex(empty,key,1,ptr,len);
                return records::finish(next);}}
            pub fn tool_main(input_ptr:i64,input_len:i64)->i64 ! {{Alloc}} {{return records::hex(input_ptr,input_len);}}"
        )).expect("label caller");
        fixture.lock();
        let output = Command::new(env!("CARGO_BIN_EXE_sigil"))
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
    let fixture = Fixture::probe("return records::hex(input_ptr,input_len);");
    let package = fixture.compile();
    assert_eq!(
        execute(&package, b"abc").expect("control").output,
        b"\"616263\""
    );
    for (fuel, engine, memory) in [
        (1, 10_000_000, 16 * 1024 * 1024),
        (500_000, 1, 16 * 1024 * 1024),
        (500_000, 10_000_000, 1),
    ] {
        assert!(
            sigil_runtime::execute_ephemeral_with_budgets(
                &package.compilation.wasm_inner,
                b"abc",
                fuel,
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
fn records_live_copy_hex_and_validation_faults_are_observed() {
    let key = text_literal("key", b"v");
    for (body, input, needle, replacement) in [
        (
            "return records::hex(input_ptr,input_len);".to_string(),
            b"\xab\xfe".as_slice(),
            "return value + 87;",
            "return value + 88;",
        ),
        (
            format!(
                "{key}let doc=records::new(128);let next=records::put_json(doc,key,1,input_ptr,input_len);return records::finish(next);"
            ),
            b"123",
            "store8(dst + i, load8(src + i));",
            "store8(dst + i, 48);",
        ),
        (
            format!("{key}return records::field(input_ptr,input_len,key,1);"),
            b"{\"v\":1}garbage",
            "let valid = json::validate(ptr, len); if valid < 0 { return valid; } else {}",
            "let valid = 0;",
        ),
        (
            format!(
                "{key}let doc=records::new(128);let next=records::put_f64le(doc,key,1,input_ptr,1);return records::finish(next);"
            ),
            b"\x00\x00\x00\x00\x00\x00\xf0\x7f",
            "if load8(ptr + i + 7) % 128 == 127 && load8(ptr + i + 6) / 16 == 15 { return -422; } else {}",
            "if false { return -422; } else {}",
        ),
    ] {
        let clean = Fixture::probe(&body);
        let baseline = execute(&clean.compile(), input);
        let mutant = Fixture::probe(&body);
        mutant.mutate(needle, replacement);
        let result = execute(&mutant.compile(), input);
        match (baseline, result) {
            (Ok(a), Ok(b)) => assert_ne!(a.output, b.output, "live mutation {needle}"),
            (Ok(_), Err(_)) | (Err(_), Ok(_)) => {}
            (Err(a), Err(b)) => assert_ne!(format!("{a:?}"), format!("{b:?}")),
        }
    }
}
