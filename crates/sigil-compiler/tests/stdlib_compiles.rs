//! Phase 5a-3: smoke test that every stdlib module compiles cleanly.
//!
//! Runs `compile_named_module` on each `stdlib/sigil/*.sigil` file and
//! asserts a successful compile. Catches regressions in cross-module
//! compilation (5a-1) and FFI shim signatures (5a-2) that would
//! otherwise only surface when an agent-written tool tried to use the
//! stdlib.
//!
//! Determinism per I6 is also verified for each module (compiled twice,
//! byte-identical wasm).

use std::path::PathBuf;

use sigil_compiler::compile_named_module;

fn stdlib_dir() -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    // CARGO_MANIFEST_DIR is .../crates/sigil-compiler — go up two and
    // into stdlib/sigil.
    p.push("..");
    p.push("..");
    p.push("stdlib");
    p.push("sigil");
    p
}

fn module_path(name: &str) -> PathBuf {
    let mut p = stdlib_dir();
    p.push(format!("{name}.sigil"));
    p
}

fn assert_compiles(name: &str) {
    let path = module_path(name);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("could not read stdlib/sigil/{name}.sigil: {e}"));
    let result = compile_named_module(format!("stdlib/{name}.sigil"), source);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!(
            "stdlib/{name}.sigil failed to compile: {} diagnostic(s) {:?}",
            err.diagnostics().len(),
            codes
        );
    }
}

fn assert_compile_deterministic(name: &str) {
    let path = module_path(name);
    let source = std::fs::read_to_string(&path).expect("read source");
    let a =
        compile_named_module(format!("stdlib/{name}.sigil"), source.clone()).expect("compile 1");
    let b = compile_named_module(format!("stdlib/{name}.sigil"), source).expect("compile 2");
    assert_eq!(
        a.wasm_inner, b.wasm_inner,
        "stdlib/{name}.sigil wasm_inner must be byte-identical (I6)"
    );
    assert_eq!(
        a.wasm_outer, b.wasm_outer,
        "stdlib/{name}.sigil wasm_outer must be byte-identical (I6)"
    );
}

#[test]
fn fs_compiles() {
    assert_compiles("fs");
    assert_compile_deterministic("fs");
}

#[test]
fn crypto_compiles() {
    assert_compiles("crypto");
    assert_compile_deterministic("crypto");
}

#[test]
fn time_compiles() {
    assert_compiles("time");
    assert_compile_deterministic("time");
}

#[test]
fn random_compiles() {
    assert_compiles("random");
    assert_compile_deterministic("random");
}

#[test]
fn http_compiles() {
    assert_compiles("http");
    assert_compile_deterministic("http");
}

#[test]
fn json_compiles() {
    assert_compiles("json");
    assert_compile_deterministic("json");
}

#[test]
fn kv_compiles() {
    assert_compiles("kv");
    assert_compile_deterministic("kv");
}

#[test]
fn abi_compiles() {
    assert_compiles("abi");
    assert_compile_deterministic("abi");
}

#[test]
fn string_helpers_compiles() {
    assert_compiles("string_helpers");
    assert_compile_deterministic("string_helpers");
}

#[test]
fn tool_using_abi_stdlib_compiles() {
    // `abi` is inner-ring (pure compute on packed i64 values), so an
    // inner-ring tool can `use sigil::abi;` without #[trusted].
    let abi = std::fs::read_to_string(module_path("abi")).expect("read abi.sigil");
    let tool = r#"
module tool;

use sigil::abi;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let packed: i64 = abi::pack(input_ptr, input_len);
    let p: i64 = abi::unpack_ptr(packed);
    let l: i64 = abi::unpack_len(packed);
    return p + l;
}
"#;
    let combined = format!("{abi}\n{tool}");
    let result = compile_named_module("tool_using_abi.sigil", combined);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile, got: {codes:?}");
    }
}

/// Sanity: tools using stdlib modules compile when stdlib is included
/// in the same compilation. Verifies the cross-module dispatch from
/// PR #18 wires up correctly with real stdlib content.
#[test]
fn tool_using_fs_stdlib_compiles() {
    let fs = std::fs::read_to_string(module_path("fs")).expect("read fs.sigil");
    let tool = r#"
#[ring(outer)] #[trusted]
module tool;

use sigil::fs;

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FsIO, Alloc, FFI, Unsafe } {
    return fs::read(input_ptr, input_len);
}
"#;
    let combined = format!("{fs}\n{tool}");
    let result = compile_named_module("tool_using_fs.sigil", combined);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile, got: {codes:?}");
    }
}

#[test]
fn z3_compiles() {
    // Self-hosting Cap<Z3>: the new `z3` stdlib module must compile and be
    // deterministic, exactly like every other FFI-backed stdlib module.
    assert_compiles("z3");
    assert_compile_deterministic("z3");
}

#[test]
fn tool_using_z3_stdlib_compiles() {
    // Positive: a tool that `use sigil::z3;` and declares the `Z3Solve`
    // effect compiles — proving cross-module use-resolution + effect
    // propagation for the Cap<Z3> module (stdlib in the same compile unit,
    // mirroring `tool_using_fs_stdlib_compiles`).
    let z3 = std::fs::read_to_string(module_path("z3")).expect("read z3.sigil");
    let tool = r#"
#[ring(outer)] #[trusted]
module tool;

use sigil::z3;

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Z3Solve, FFI, Unsafe } {
    return z3::check(input_ptr, input_len);
}
"#;
    let combined = format!("{z3}\n{tool}");
    let result = compile_named_module("tool_using_z3.sigil", combined);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile, got: {codes:?}");
    }
}

#[test]
fn tool_using_z3_without_effect_is_rejected() {
    // Negative: Z3 is effect-gated, NOT ambient. A tool that calls
    // `z3::check` but OMITS `Z3Solve` from its effect row must be rejected
    // (E001 — undeclared effect required by callee), proving the capability
    // is tracked through the type system rather than silently reachable.
    let z3 = std::fs::read_to_string(module_path("z3")).expect("read z3.sigil");
    let tool = r#"
#[ring(outer)] #[trusted]
module tool;

use sigil::z3;

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FFI, Unsafe } {
    return z3::check(input_ptr, input_len);
}
"#;
    let combined = format!("{z3}\n{tool}");
    let err = compile_named_module("tool_using_z3_no_effect.sigil", combined)
        .expect_err("omitting Z3Solve must be rejected");
    let codes: Vec<String> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect();
    assert!(
        codes.iter().any(|c| c == "E001"),
        "expected E001 (undeclared effect Z3Solve), got: {codes:?}"
    );
}

#[test]
fn tool_using_kv_without_effect_is_rejected() {
    // Negative: kv is effect-gated, NOT ambient. A tool that calls
    // `kv::get` but OMITS `KvIO` from its effect row must be rejected
    // (E001), proving the storage capability is tracked through the
    // type system — same contract as the z3 test above.
    let kv = std::fs::read_to_string(module_path("kv")).expect("read kv.sigil");
    let tool = r#"
#[ring(outer)] #[trusted]
module tool;

use sigil::kv;

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc, FFI, Unsafe } {
    return kv::get(input_ptr, input_len, input_ptr, input_len);
}
"#;
    let combined = format!("{kv}\n{tool}");
    let err = compile_named_module("tool_using_kv_no_effect.sigil", combined)
        .expect_err("omitting KvIO must be rejected");
    let codes: Vec<String> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect();
    assert!(
        codes.iter().any(|c| c == "E001"),
        "expected E001 (undeclared effect KvIO), got: {codes:?}"
    );
}

#[test]
fn tool_using_json_stdlib_inner_ring_compiles() {
    // `json` is inner-ring (no FFI), so an inner-ring tool can use it
    // without `#[ring(outer)] #[trusted]`. Verifies the no-escalation
    // path documented in STDLIB.md.
    let json = std::fs::read_to_string(module_path("json")).expect("read json.sigil");
    let tool = r#"
module tool;

use sigil::json;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let key_ptr: i64 = input_ptr;
    let key_len: i64 = 4;
    return json::parse_field(input_ptr, input_len, key_ptr, key_len);
}
"#;
    let combined = format!("{json}\n{tool}");
    let result = compile_named_module("tool_using_json.sigil", combined);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile, got: {codes:?}");
    }
}
