//! KV storage shims (`kv_get` / `kv_put` / `kv_delete`) — grant-gated,
//! namespace-scoped, and DURABLE: values put in one ephemeral execution
//! are readable in later executions. That cross-run test is the point
//! of the capability; everything else guards the boundary (fail-closed
//! grants, read/write separation, namespace isolation, size caps).
//!
//! Tools declare the externs directly (same style as `ffi_shims.rs`);
//! one test additionally composes the real `stdlib/sigil/kv.sigil`
//! wrapper to prove the `use sigil::kv;` + `KvIO` effect-row path.

use std::path::{Path, PathBuf};

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::{IoGrants, KvGrant, KvWriteGrant, MAX_GRANTS_PER_CATEGORY, execute_ephemeral};

const FUEL: u64 = 50_000_000;

const KV_EXTERNS: &str = "extern \"C\" fn kv_get(ns: i32, ns_len: i32, key: i32, key_len: i32) -> i64 ! { FFI, Unsafe };\n\
extern \"C\" fn kv_put(ns: i32, ns_len: i32, key: i32, key_len: i32, val: i32, val_len: i32) -> i64 ! { FFI, Unsafe };\n\
extern \"C\" fn kv_delete(ns: i32, ns_len: i32, key: i32, key_len: i32) -> i64 ! { FFI, Unsafe };\n";

/// Fresh scratch directory for one test. Best-effort removed on drop.
struct KvDir(PathBuf);

impl KvDir {
    fn new(test: &str) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "sigil_kv_{test}_{}_{:x}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).expect("create kv scratch dir");
        Self(dir)
    }
    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for KvDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Emit statements materializing `bytes` in guest memory, binding
/// `<name>_ptr: i32`.
fn store_buf(name: &str, bytes: &[u8]) -> String {
    let mut s = format!("    let {name}_buf: i64 = alloc({});\n", bytes.len().max(1));
    for (i, b) in bytes.iter().enumerate() {
        s.push_str(&format!("    store8({name}_buf + {i}, {b});\n"));
    }
    s.push_str(&format!("    let {name}_ptr: i32 = {name}_buf.as_i32();\n"));
    s
}

fn tool(body: &str) -> String {
    format!(
        "#[ring(outer)] #[trusted] module tool;\n{KV_EXTERNS}\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! {{ Alloc, FFI, Unsafe }} {{\n{body}}}\n"
    )
}

/// Tool: put(ns, key, <run input>) — returns the shim result directly
/// (0 = success = empty output).
fn put_tool(ns: &str, key: &[u8]) -> String {
    tool(&format!(
        "{}{}    return kv_put(ns_ptr, {}, key_ptr, {}, input_ptr, input_len);\n",
        store_buf("ns", ns.as_bytes()),
        store_buf("key", key),
        ns.len(),
        key.len()
    ))
}

/// Tool: get(ns, key) — returns the packed value (output = value bytes).
fn get_tool(ns: &str, key: &[u8]) -> String {
    tool(&format!(
        "{}{}    return kv_get(ns_ptr, {}, key_ptr, {});\n",
        store_buf("ns", ns.as_bytes()),
        store_buf("key", key),
        ns.len(),
        key.len()
    ))
}

/// Tool: delete(ns, key) — returns the shim result directly.
fn delete_tool(ns: &str, key: &[u8]) -> String {
    tool(&format!(
        "{}{}    return kv_delete(ns_ptr, {}, key_ptr, {});\n",
        store_buf("ns", ns.as_bytes()),
        store_buf("key", key),
        ns.len(),
        key.len()
    ))
}

/// Tool: get(ns, <run input as KEY>) — for driving oversized keys.
fn get_with_input_key_tool(ns: &str) -> String {
    tool(&format!(
        "{}    return kv_get(ns_ptr, {}, input_ptr, input_len);\n",
        store_buf("ns", ns.as_bytes()),
        ns.len()
    ))
}

fn read_grants(ns: &str, root: &Path) -> IoGrants {
    IoGrants {
        kv: vec![KvGrant {
            namespace: ns.to_owned(),
            root: root.to_path_buf(),
        }],
        ..Default::default()
    }
}

fn write_grants(ns: &str, root: &Path) -> IoGrants {
    IoGrants {
        kv_write: vec![KvWriteGrant {
            namespace: ns.to_owned(),
            root: root.to_path_buf(),
        }],
        ..Default::default()
    }
}

fn rw_grants(ns: &str, root: &Path) -> IoGrants {
    IoGrants {
        kv: vec![KvGrant {
            namespace: ns.to_owned(),
            root: root.to_path_buf(),
        }],
        kv_write: vec![KvWriteGrant {
            namespace: ns.to_owned(),
            root: root.to_path_buf(),
        }],
        ..Default::default()
    }
}

/// Ok(output bytes) or Err(positive magnitude of the negative return).
fn run(source: &str, input: &[u8], grants: &IoGrants) -> Result<Vec<u8>, i64> {
    let compiled = compile_tool(source).expect("tool should compile");
    match execute_ephemeral(&compiled.wasm, input, FUEL, grants) {
        Ok(result) => Ok(result.output),
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message
                .find(prefix)
                .unwrap_or_else(|| panic!("genuine trap: {message}"))
                + prefix.len();
            let end = message[start..].find(')').expect("sentinel close paren");
            Err(message[start..start + end].parse::<i64>().expect("code"))
        }
        Err(other) => panic!("exec error: {other:?}"),
    }
}

// ── Fail-closed boundary ──────────────────────────────────────────────────

#[test]
fn kv_fails_closed_without_grants() {
    let none = IoGrants::none();
    assert_eq!(run(&get_tool("ns", b"k"), b"", &none), Err(403));
    assert_eq!(run(&put_tool("ns", b"k"), b"v", &none), Err(403));
    assert_eq!(run(&delete_tool("ns", b"k"), b"", &none), Err(403));
}

#[test]
fn kv_read_and_write_grants_are_separate() {
    let dir = KvDir::new("rw_sep");
    let read_only = read_grants("ns", dir.path());
    let write_only = write_grants("ns", dir.path());

    // Read grant does not confer write.
    assert_eq!(run(&put_tool("ns", b"k"), b"v", &read_only), Err(403));
    assert_eq!(run(&delete_tool("ns", b"k"), b"", &read_only), Err(403));
    // Write grant does not confer read.
    assert_eq!(run(&put_tool("ns", b"k"), b"v", &write_only), Ok(vec![]));
    assert_eq!(run(&get_tool("ns", b"k"), b"", &write_only), Err(403));
}

#[test]
fn kv_namespace_must_match_grant() {
    let dir = KvDir::new("ns_match");
    let grants = rw_grants("granted", dir.path());
    assert_eq!(run(&get_tool("other", b"k"), b"", &grants), Err(403));
    assert_eq!(run(&put_tool("other", b"k"), b"v", &grants), Err(403));
}

// ── Core semantics ────────────────────────────────────────────────────────

#[test]
fn kv_get_missing_key_is_404() {
    let dir = KvDir::new("missing");
    let grants = read_grants("ns", dir.path());
    assert_eq!(run(&get_tool("ns", b"absent"), b"", &grants), Err(404));
}

#[test]
fn kv_durability_across_ephemeral_runs() {
    // THE capability headline: state survives the one-shot runtime.
    let dir = KvDir::new("durable");
    let value = b"counter=41; survives the process";

    let put = run(
        &put_tool("app", b"state"),
        value,
        &write_grants("app", dir.path()),
    );
    assert_eq!(put, Ok(vec![]), "put should succeed");

    // Entirely separate execution: fresh store, fresh memory, read grant.
    let got = run(
        &get_tool("app", b"state"),
        b"",
        &read_grants("app", dir.path()),
    );
    assert_eq!(got, Ok(value.to_vec()), "value must survive across runs");
}

#[test]
fn kv_put_overwrites() {
    let dir = KvDir::new("overwrite");
    let grants = rw_grants("ns", dir.path());
    assert_eq!(run(&put_tool("ns", b"k"), b"first", &grants), Ok(vec![]));
    assert_eq!(run(&put_tool("ns", b"k"), b"second", &grants), Ok(vec![]));
    assert_eq!(
        run(&get_tool("ns", b"k"), b"", &grants),
        Ok(b"second".to_vec())
    );
}

#[test]
fn kv_delete_then_get() {
    let dir = KvDir::new("delete");
    let grants = rw_grants("ns", dir.path());
    assert_eq!(run(&put_tool("ns", b"k"), b"v", &grants), Ok(vec![]));
    assert_eq!(run(&delete_tool("ns", b"k"), b"", &grants), Ok(vec![]));
    assert_eq!(run(&get_tool("ns", b"k"), b"", &grants), Err(404));
    // Deleting an absent key reports 404, not success.
    assert_eq!(run(&delete_tool("ns", b"k"), b"", &grants), Err(404));
}

#[test]
fn kv_namespaces_are_isolated() {
    let dir_a = KvDir::new("iso_a");
    let dir_b = KvDir::new("iso_b");
    let grants = IoGrants {
        kv: vec![
            KvGrant {
                namespace: "a".into(),
                root: dir_a.path().to_path_buf(),
            },
            KvGrant {
                namespace: "b".into(),
                root: dir_b.path().to_path_buf(),
            },
        ],
        kv_write: vec![
            KvWriteGrant {
                namespace: "a".into(),
                root: dir_a.path().to_path_buf(),
            },
            KvWriteGrant {
                namespace: "b".into(),
                root: dir_b.path().to_path_buf(),
            },
        ],
        ..Default::default()
    };
    // Same key, different namespaces, different values.
    assert_eq!(run(&put_tool("a", b"k"), b"from-a", &grants), Ok(vec![]));
    assert_eq!(run(&put_tool("b", b"k"), b"from-b", &grants), Ok(vec![]));
    assert_eq!(
        run(&get_tool("a", b"k"), b"", &grants),
        Ok(b"from-a".to_vec())
    );
    assert_eq!(
        run(&get_tool("b", b"k"), b"", &grants),
        Ok(b"from-b".to_vec())
    );
}

#[test]
fn kv_binary_keys_and_values_roundtrip() {
    let dir = KvDir::new("binary");
    let grants = rw_grants("bin", dir.path());
    let key: &[u8] = &[0x00, 0xFF, 0x2F, 0x2E, 0x2E, 0x5C, 0x0A];
    let value: &[u8] = &[0u8, 1, 2, 255, 254, 128, 0, 10, 13];
    assert_eq!(run(&put_tool("bin", key), value, &grants), Ok(vec![]));
    assert_eq!(run(&get_tool("bin", key), b"", &grants), Ok(value.to_vec()));
}

#[test]
fn kv_empty_value_roundtrips() {
    let dir = KvDir::new("empty_val");
    let grants = rw_grants("ns", dir.path());
    assert_eq!(run(&put_tool("ns", b"k"), b"", &grants), Ok(vec![]));
    // Present-but-empty is Ok(empty), NOT -404.
    assert_eq!(run(&get_tool("ns", b"k"), b"", &grants), Ok(vec![]));
}

// ── Size caps ─────────────────────────────────────────────────────────────

#[test]
fn kv_key_over_1k_is_413() {
    let dir = KvDir::new("bigkey");
    let grants = read_grants("ns", dir.path());
    let big_key = vec![b'k'; 1025];
    assert_eq!(
        run(&get_with_input_key_tool("ns"), &big_key, &grants),
        Err(413)
    );
    // Exactly at the cap is allowed (missing → 404, not 413).
    let at_cap = vec![b'k'; 1024];
    assert_eq!(
        run(&get_with_input_key_tool("ns"), &at_cap, &grants),
        Err(404)
    );
}

#[test]
fn kv_value_over_5mb_is_413() {
    let dir = KvDir::new("bigval");
    let grants = write_grants("ns", dir.path());
    let big = vec![0xABu8; 5 * 1024 * 1024 + 1];
    assert_eq!(run(&put_tool("ns", b"k"), &big, &grants), Err(413));
}

// ── Grant plumbing ────────────────────────────────────────────────────────

#[test]
fn r808_kv_categories_capped() {
    let over: Vec<KvGrant> = (0..=MAX_GRANTS_PER_CATEGORY)
        .map(|i| KvGrant {
            namespace: format!("ns{i}"),
            root: PathBuf::from("/tmp/kv"),
        })
        .collect();
    let grants = IoGrants {
        kv: over,
        ..Default::default()
    };
    let err = grants.validate().expect_err("kv over cap must fail");
    assert_eq!(err.category, "kv");

    let over_w: Vec<KvWriteGrant> = (0..=MAX_GRANTS_PER_CATEGORY)
        .map(|i| KvWriteGrant {
            namespace: format!("ns{i}"),
            root: PathBuf::from("/tmp/kv"),
        })
        .collect();
    let grants_w = IoGrants {
        kv_write: over_w,
        ..Default::default()
    };
    let err_w = grants_w
        .validate()
        .expect_err("kv_write over cap must fail");
    assert_eq!(err_w.category, "kv_write");
}

#[test]
fn kv_grant_root_resolution() {
    let grants = rw_grants("ns", Path::new("/data/kv"));
    assert_eq!(
        grants.kv_read_root("ns"),
        Some(Path::new("/data/kv")),
        "read root resolves for granted namespace"
    );
    assert_eq!(grants.kv_read_root("other"), None, "ungranted = None");
    assert_eq!(grants.kv_write_root("ns"), Some(Path::new("/data/kv")));
    assert_eq!(grants.kv_write_root("other"), None);
}

// ── Stdlib wrapper composition ────────────────────────────────────────────

#[test]
fn kv_via_stdlib_wrapper_roundtrips() {
    // Compose the REAL stdlib/sigil/kv.sigil (tool first, stdlib
    // appended — compose.py order) and drive put + get through the
    // `kv::` wrappers with the full `KvIO` effect row.
    // Both wrapper calls happen BEFORE branching on the @Internal
    // put result: the mainline taint checker tracks continuation
    // taint after control-dependent early exits, and the wrappers'
    // params are @Public.
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("..");
    p.push("..");
    p.push("stdlib");
    p.push("sigil");
    p.push("kv.sigil");
    let stdlib_kv = std::fs::read_to_string(&p).expect("read stdlib/sigil/kv.sigil");

    let tool_src = format!(
        "#[ring(outer)] #[trusted] module tool;\n\
         use sigil::kv;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! {{ KvIO, Alloc, FFI, Unsafe }} {{\n\
         {}{}    let put_rc: i64 @Internal = kv::put(ns_ptr, 5, key_ptr, 4, input_ptr, input_len);\n\
         \x20   let got: i64 @Internal = kv::get(ns_ptr, 5, key_ptr, 4);\n\
         \x20   if put_rc < 0 {{\n        return put_rc;\n    }} else {{\n    }}\n\
         \x20   return got;\n}}\n\n{stdlib_kv}",
        store_buf("ns", b"cache"),
        store_buf("key", b"item")
    );

    let dir = KvDir::new("stdlib_wrap");
    let grants = rw_grants("cache", dir.path());
    let value = b"stdlib wrapper path works";
    assert_eq!(run(&tool_src, value, &grants), Ok(value.to_vec()));
}
