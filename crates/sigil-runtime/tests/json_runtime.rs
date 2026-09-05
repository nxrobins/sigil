//! json v2 codec — end-to-end execution tests over the REAL stdlib
//! source (`stdlib/sigil/json.sigil` composed with a tool module, same
//! order as `bench/src/sigil_bench/compose.py`: tool first, stdlib
//! appended).
//!
//! Success paths read the tool's packed-pointer output bytes; error
//! paths decode the `tool returned error (K)` trap sentinel, where K is
//! the positive magnitude of the negative return (400/404/429/430).
//! Count-returning fns (`array_len`, `validate`) are wrapped as
//! `return 0 - (n + 1000000);` so both counts and error codes travel
//! through the sentinel: n = K - 1000000.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Generous budget: adversarial fixtures (10k fields) need far more
/// fuel than the compiler's static estimate.
const FUEL: u64 = 500_000_000;

fn json_stdlib_source() -> String {
    let mut p = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("..");
    p.push("..");
    p.push("stdlib");
    p.push("sigil");
    p.push("json.sigil");
    std::fs::read_to_string(&p).expect("read stdlib/sigil/json.sigil")
}

fn compose(tool_body: &str) -> String {
    format!(
        "module tool;\n\nuse sigil::json;\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{tool_body}\n}}\n\n{}",
        json_stdlib_source()
    )
}

/// Emit `let key_ptr = alloc(N); store8...` lines materializing `key`.
fn key_stores(key: &[u8]) -> String {
    let mut s = format!("    let key_ptr: i64 = alloc({});\n", key.len().max(1));
    for (idx, b) in key.iter().enumerate() {
        s.push_str(&format!("    store8(key_ptr + {idx}, {b});\n"));
    }
    s
}

/// Ok(output bytes) or Err(positive error magnitude from the sentinel).
fn run(tool_body: &str, input: &[u8]) -> Result<Vec<u8>, i64> {
    let source = compose(tool_body);
    let result = compile_tool(&source)
        .unwrap_or_else(|e| panic!("tool should compile, got: {e:?}\n--- body ---\n{tool_body}"));
    match execute_ephemeral(&result.wasm, input, FUEL, &IoGrants::none()) {
        Ok(exec) => Ok(exec.output),
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message
                .find(prefix)
                .unwrap_or_else(|| panic!("genuine trap (not a sentinel): {message}"))
                + prefix.len();
            let end = message[start..].find(')').expect("malformed sentinel");
            Err(message[start..start + end]
                .parse::<i64>()
                .expect("sentinel magnitude parses"))
        }
        Err(other) => panic!("exec error: {other:?}"),
    }
}

fn parse_field_body(key: &[u8]) -> String {
    format!(
        "{}    return json::parse_field(input_ptr, input_len, key_ptr, {});",
        key_stores(key),
        key.len()
    )
}

fn run_parse_field(input: &str, key: &[u8]) -> Result<Vec<u8>, i64> {
    run(&parse_field_body(key), input.as_bytes())
}

fn run_parse_index(input: &str, index: i64) -> Result<Vec<u8>, i64> {
    run(
        &format!("    return json::parse_index(input_ptr, input_len, {index});"),
        input.as_bytes(),
    )
}

/// Run an `n = json::<fn>(...)` count/status wrapper; decode n.
fn run_counting(call: &str, input: &[u8]) -> i64 {
    let body = format!("    let n: i64 = {call};\n    return 0 - (n + 1000000);");
    match run(&body, input) {
        Err(k) => k - 1_000_000,
        Ok(out) => panic!("counting wrapper must trap, got output {out:?}"),
    }
}

fn validate_of(input: &str) -> i64 {
    run_counting("json::validate(input_ptr, input_len)", input.as_bytes())
}

fn array_len_of(input: &str) -> i64 {
    run_counting("json::array_len(input_ptr, input_len)", input.as_bytes())
}

// ─── parse_field ────────────────────────────────────────────────────────

#[test]
fn parse_field_v1_compat_and_scalars() {
    // (input, key, expected output)
    let ok: &[(&str, &[u8], &[u8])] = &[
        // The two bench task061 fixtures, byte-for-byte.
        (r#"{"name": "alice", "age": 30}"#, b"name", b"alice"),
        (r#"{"id": 42, "name": "bob"}"#, b"name", b"bob"),
        (r#"{"name": "alice", "age": 30}"#, b"age", b"30"),
        (r#"{"a": true, "b": false, "c": null}"#, b"b", b"false"),
        (r#"{"a": true, "b": false, "c": null}"#, b"c", b"null"),
        // Full number grammar comes back raw.
        (r#"{"pi": 3.14159}"#, b"pi", b"3.14159"),
        (r#"{"e": -0.5e+10}"#, b"e", b"-0.5e+10"),
        (r#"{"z": -0}"#, b"z", b"-0"),
        // Later field after values of every kind.
        (
            r#"{"s": "x", "n": 1.5e2, "t": true, "o": {"k": [1]}, "last": "yes"}"#,
            b"last",
            b"yes",
        ),
    ];
    let mut failures = Vec::new();
    for (input, key, want) in ok {
        match run_parse_field(input, key) {
            Ok(out) if out == *want => {}
            got => failures.push(format!(
                "{input} [{}] => {got:?}, want {:?}",
                String::from_utf8_lossy(key),
                String::from_utf8_lossy(want)
            )),
        }
    }
    assert!(failures.is_empty(), "divergences:\n{}", failures.join("\n"));
}

#[test]
fn parse_field_decodes_escapes() {
    let ok: &[(&str, &[u8], &[u8])] = &[
        (
            r#"{"a": "he said \"hi\"\nover\tthere"}"#,
            b"a",
            b"he said \"hi\"\nover\tthere",
        ),
        (r#"{"a": "back\\slash \/ fwd"}"#, b"a", b"back\\slash / fwd"),
        (r#"{"a": "\b\f\r"}"#, b"a", b"\x08\x0C\x0D"),
        // \uXXXX: ASCII, 2-byte, 3-byte, and a surrogate pair (4-byte).
        (r#"{"u": "\u0041"}"#, b"u", b"A"),
        (r#"{"u": "\u00e9"}"#, b"u", "é".as_bytes()),
        (r#"{"u": "\u4e2d"}"#, b"u", "中".as_bytes()),
        (r#"{"u": "\ud83d\ude00"}"#, b"u", "😀".as_bytes()),
        (r#"{"u": "x\u0000y"}"#, b"u", b"x\x00y"),
        // Raw UTF-8 passes through untouched.
        (r#"{"u": "café"}"#, b"u", "café".as_bytes()),
    ];
    let mut failures = Vec::new();
    for (input, key, want) in ok {
        match run_parse_field(input, key) {
            Ok(out) if out == *want => {}
            got => failures.push(format!("{input} => {got:?}, want {want:?}")),
        }
    }
    assert!(failures.is_empty(), "divergences:\n{}", failures.join("\n"));
}

#[test]
fn parse_field_matches_escaped_keys() {
    // {"a\nb": 1} found by the decoded 3-byte key.
    assert_eq!(
        run_parse_field(r#"{"a\nb": 1}"#, b"a\nb"),
        Ok(b"1".to_vec())
    );
    // Escaped backslash in the key.
    assert_eq!(
        run_parse_field(r#"{"a\\b": 2}"#, b"a\\b"),
        Ok(b"2".to_vec())
    );
    // \u-escaped key matches its UTF-8 form.
    assert_eq!(
        run_parse_field(r#"{"\u00e9": 3}"#, "é".as_bytes()),
        Ok(b"3".to_vec())
    );
    // The RAW escape bytes must NOT match (comparison is post-decode).
    assert_eq!(run_parse_field(r#"{"a\nb": 1}"#, b"a\\nb"), Err(404));
}

#[test]
fn parse_field_returns_nested_raw_slices() {
    let ok: &[(&str, &[u8], &[u8])] = &[
        (
            r#"{"cfg": {"a": [1, 2]}, "x": 1}"#,
            b"cfg",
            b"{\"a\": [1, 2]}",
        ),
        (
            r#"{"arr": [1, {"b": 2}, [3]], "x": 1}"#,
            b"arr",
            b"[1, {\"b\": 2}, [3]]",
        ),
        (r#"{"o": {}}"#, b"o", b"{}"),
        (r#"{"o": [ ]}"#, b"o", b"[ ]"),
        // Interior whitespace and strings-with-brackets survive byte-exact.
        (
            r#"{"o": { "s" : "}]" , "n" : [ 1 ] }}"#,
            b"o",
            b"{ \"s\" : \"}]\" , \"n\" : [ 1 ] }",
        ),
    ];
    let mut failures = Vec::new();
    for (input, key, want) in ok {
        match run_parse_field(input, key) {
            Ok(out) if out == *want => {}
            got => failures.push(format!(
                "{input} => {got:?}, want {:?}",
                String::from_utf8_lossy(want)
            )),
        }
    }
    assert!(failures.is_empty(), "divergences:\n{}", failures.join("\n"));
}

#[test]
fn parse_field_error_codes() {
    let errs: &[(&str, &[u8], i64)] = &[
        // Not found.
        (r#"{"name": "alice"}"#, b"missing", 404),
        (r#"{}"#, b"name", 404),
        // Malformed documents.
        (r#""#, b"k", 400),
        (r#"[1, 2]"#, b"k", 400),
        (r#"{"a" 1}"#, b"a", 400),
        (r#"{"a": 1,}"#, b"k", 400),
        (r#"{"a": 1"#, b"k", 400),
        (r#"{'a': 1}"#, b"a", 400),
        // Strict values, even on fields being skipped.
        (r#"{"a": 01, "k": 2}"#, b"k", 400),
        (r#"{"a": tru, "k": 2}"#, b"k", 400),
        (r#"{"a": nulL, "k": 2}"#, b"k", 400),
        (r#"{"a": +1, "k": 2}"#, b"k", 400),
        (r#"{"a": 1., "k": 2}"#, b"k", 400),
        (r#"{"a": .5, "k": 2}"#, b"k", 400),
        (r#"{"a": 1e, "k": 2}"#, b"k", 400),
        // Bad escapes / string bytes.
        (r#"{"a": "\q"}"#, b"a", 400),
        (r#"{"a": "\u12g4"}"#, b"a", 400),
        (r#"{"a": "\u12"}"#, b"a", 400),
        (r#"{"a": "\ud800"}"#, b"a", 400),
        (r#"{"a": "\ude00"}"#, b"a", 400),
        (r#"{"a": "\ud800\u0041"}"#, b"a", 400),
        ("{\"a\": \"raw\ncontrol\"}", b"a", 400),
    ];
    let mut failures = Vec::new();
    for (input, key, want) in errs {
        match run_parse_field(input, key) {
            Err(k) if k == *want => {}
            got => failures.push(format!("{input:?} => {got:?}, want Err({want})")),
        }
    }
    assert!(failures.is_empty(), "divergences:\n{}", failures.join("\n"));
}

#[test]
fn parse_field_caps() {
    // Exactly 10,000 fields: scan completes, key absent => -404.
    let mut ten_k = String::from("{");
    for n in 0..10_000 {
        if n > 0 {
            ten_k.push(',');
        }
        ten_k.push_str(&format!("\"k{n}\":0"));
    }
    ten_k.push('}');
    assert_eq!(run_parse_field(&ten_k, b"absent"), Err(404));
    // The 10,000th field is still reachable.
    assert_eq!(run_parse_field(&ten_k, b"k9999"), Ok(b"0".to_vec()));

    // 10,001 fields: cap trips.
    let mut over = String::from("{");
    for n in 0..10_001 {
        if n > 0 {
            over.push(',');
        }
        over.push_str(&format!("\"k{n}\":0"));
    }
    over.push('}');
    assert_eq!(run_parse_field(&over, b"absent"), Err(429));

    // Nesting: 63 levels pass, 64 trip the depth cap — inside a field
    // value being skipped.
    let deep_ok = format!(r#"{{"d": {}1{}, "k": 5}}"#, "[".repeat(62), "]".repeat(62));
    assert_eq!(run_parse_field(&deep_ok, b"k"), Ok(b"5".to_vec()));
    let deep_err = format!(r#"{{"d": {}1{}, "k": 5}}"#, "[".repeat(64), "]".repeat(64));
    assert_eq!(run_parse_field(&deep_err, b"k"), Err(430));
}

// ─── parse_index ────────────────────────────────────────────────────────

#[test]
fn parse_index_extracts_elements() {
    let ok: &[(&str, i64, &[u8])] = &[
        (r#"[10, "x", true]"#, 0, b"10"),
        (r#"[10, "x", true]"#, 1, b"x"),
        (r#"[10, "x", true]"#, 2, b"true"),
        (r#"[[1,2],[3]]"#, 1, b"[3]"),
        (r#"[{"a": 1}]"#, 0, b"{\"a\": 1}"),
        (r#"["a\"b"]"#, 0, b"a\"b"),
        (r#"[ 1 , 2 ]"#, 1, b"2"),
    ];
    let mut failures = Vec::new();
    for (input, idx, want) in ok {
        match run_parse_index(input, *idx) {
            Ok(out) if out == *want => {}
            got => failures.push(format!("{input}[{idx}] => {got:?}, want {want:?}")),
        }
    }
    assert!(failures.is_empty(), "divergences:\n{}", failures.join("\n"));
}

#[test]
fn parse_index_error_codes() {
    assert_eq!(run_parse_index(r#"[10, "x", true]"#, 3), Err(404));
    assert_eq!(run_parse_index(r#"[]"#, 0), Err(404));
    assert_eq!(run_parse_index(r#"[1]"#, -1), Err(404));
    assert_eq!(run_parse_index(r#"{"a": 1}"#, 0), Err(400));
    assert_eq!(run_parse_index(r#"[1, 2"#, 2), Err(400));
    assert_eq!(run_parse_index(r#"[01]"#, 0), Err(400));
}

#[test]
fn extraction_is_streaming() {
    // Extraction validates only the bytes it traverses and stops once
    // the target is extracted — bytes AFTER the target (including a
    // missing closing bracket) are never inspected. Whole-document
    // strictness is `validate`'s contract, not extraction's.
    assert_eq!(run_parse_index(r#"[1, 2"#, 1), Ok(b"2".to_vec()));
    assert_eq!(run_parse_field(r#"{"a": 1"#, b"a"), Ok(b"1".to_vec()));
    assert_eq!(
        run_parse_field(r#"{"a": 1} trailing garbage"#, b"a"),
        Ok(b"1".to_vec())
    );
    // But malformed bytes BEFORE the target still fail.
    assert_eq!(run_parse_field(r#"{"x": 01, "a": 1"#, b"a"), Err(400));
    assert_eq!(validate_of(r#"{"a": 1"#), -400);
}

#[test]
fn parse_field_then_parse_index_composes() {
    // Extract a nested slice and index into it, all inside the guest.
    let body = format!(
        "{}    let cfg: i64 = json::parse_field(input_ptr, input_len, key_ptr, 3);\n\
         \x20   if cfg < 0 {{\n        return cfg;\n    }} else {{\n    }}\n\
         \x20   let cfg_ptr: i64 = cfg >> 32;\n\
         \x20   let cfg_len: i64 = cfg & 0xFFFFFFFF;\n\
         \x20   let list_key: i64 = alloc(4);\n\
         \x20   store8(list_key, 108);\n\
         \x20   store8(list_key + 1, 105);\n\
         \x20   store8(list_key + 2, 115);\n\
         \x20   store8(list_key + 3, 116);\n\
         \x20   let list: i64 = json::parse_field(cfg_ptr, cfg_len, list_key, 4);\n\
         \x20   if list < 0 {{\n        return list;\n    }} else {{\n    }}\n\
         \x20   let list_ptr: i64 = list >> 32;\n\
         \x20   let list_len: i64 = list & 0xFFFFFFFF;\n\
         \x20   return json::parse_index(list_ptr, list_len, 2);",
        key_stores(b"cfg")
    );
    let input = r#"{"cfg": {"list": [10, 20, 30]}, "x": 1}"#;
    assert_eq!(run(&body, input.as_bytes()), Ok(b"30".to_vec()));
}

// ─── array_len / validate ───────────────────────────────────────────────

#[test]
fn array_len_counts() {
    assert_eq!(array_len_of(r#"[1,"a",{"b":2},[3],true,null]"#), 6);
    assert_eq!(array_len_of(r#"[]"#), 0);
    assert_eq!(array_len_of(r#"[ 1 , 2 ]"#), 2);
    assert_eq!(array_len_of(r#"[[1,[2,[3]]]]"#), 1);
    assert_eq!(array_len_of(r#"{"a": 1}"#), -400);
    assert_eq!(array_len_of(r#"[1, 2"#), -400);
    assert_eq!(array_len_of(r#"[1,]"#), -400);
}

#[test]
fn validate_accepts_valid_documents() {
    let valid = [
        r#"{"name": "alice", "age": 30}"#,
        r#"0"#,
        r#"-0"#,
        r#"3.14"#,
        r#"-0.5e+10"#,
        r#"1e9"#,
        r#"1E-3"#,
        r#""hi""#,
        r#""\ud83d\ude00""#,
        r#"true"#,
        r#"false"#,
        r#"null"#,
        r#"[]"#,
        r#"  {  }  "#,
        r#"[[], {}, [{"a": [1]}]]"#,
        "\t[1, 2]\n",
    ];
    let mut failures = Vec::new();
    for input in valid {
        let got = validate_of(input);
        if got != 0 {
            failures.push(format!("{input:?} => {got}, want 0"));
        }
    }
    assert!(failures.is_empty(), "divergences:\n{}", failures.join("\n"));
}

#[test]
fn validate_rejects_invalid_documents() {
    let invalid: &[(&str, i64)] = &[
        ("", -400),
        ("   ", -400),
        ("01", -400),
        ("+1", -400),
        ("1.", -400),
        (".5", -400),
        ("1e", -400),
        ("1e+", -400),
        ("--1", -400),
        ("tru", -400),
        ("truex", -400),
        ("nulL", -400),
        ("{,}", -400),
        ("[1,]", -400),
        ("[,1]", -400),
        ("{\"a\":}", -400),
        ("{\"a\":1 \"b\":2}", -400),
        ("\"unterminated", -400),
        ("\"\\q\"", -400),
        ("\"\\ud800\"", -400),
        ("{}extra", -400),
        ("1 2", -400),
        ("[1] []", -400),
    ];
    let mut failures = Vec::new();
    for (input, want) in invalid {
        let got = validate_of(input);
        if got != *want {
            failures.push(format!("{input:?} => {got}, want {want}"));
        }
    }
    assert!(failures.is_empty(), "divergences:\n{}", failures.join("\n"));
}

#[test]
fn validate_depth_cap() {
    let ok = format!("{}1{}", "[".repeat(63), "]".repeat(63));
    assert_eq!(validate_of(&ok), 0);
    let too_deep = format!("{}1{}", "[".repeat(64), "]".repeat(64));
    assert_eq!(validate_of(&too_deep), -430);
    // Unbalanced deep input must be malformed, not accepted.
    let unbalanced = format!("{}1", "[".repeat(50));
    assert_eq!(validate_of(&unbalanced), -400);
    // Mixed-kind nesting: mismatched closers rejected.
    assert_eq!(validate_of(r#"[{"a": 1]}"#), -400);
    assert_eq!(validate_of(r#"{"a": [1}]"#), -400);
}

// ─── escape_string ──────────────────────────────────────────────────────

#[test]
fn escape_string_encodes() {
    let cases: &[(&[u8], &[u8])] = &[
        (b"", b"\"\""),
        (b"plain", b"\"plain\""),
        (b"he\"llo", b"\"he\\\"llo\""),
        (b"back\\slash", b"\"back\\\\slash\""),
        (b"a\nb\tc\rd\x08e\x0Cf", b"\"a\\nb\\tc\\rd\\be\\ff\""),
        (b"\x00\x01\x1F", b"\"\\u0000\\u0001\\u001f\""),
        // UTF-8 passes through raw (no \u escaping of multibyte).
        ("café 😀".as_bytes(), "\"café 😀\"".as_bytes()),
    ];
    let body = "    return json::escape_string(input_ptr, input_len);";
    let mut failures = Vec::new();
    for (input, want) in cases {
        match run(body, input) {
            Ok(out) if out == *want => {}
            got => failures.push(format!("{input:?} => {got:?}, want {want:?}")),
        }
    }
    assert!(failures.is_empty(), "divergences:\n{}", failures.join("\n"));
}

#[test]
fn escape_string_roundtrips_through_parse_index() {
    // Guest-side roundtrip: escape the input, wrap it as `[<escaped>]`,
    // parse element 0 back out — must reproduce the input bytes.
    let body = "    let esc: i64 = json::escape_string(input_ptr, input_len);\n\
                \x20   if esc < 0 {\n        return esc;\n    } else {\n    }\n\
                \x20   let esc_ptr: i64 = esc >> 32;\n\
                \x20   let esc_len: i64 = esc & 0xFFFFFFFF;\n\
                \x20   let doc: i64 = alloc(esc_len + 2);\n\
                \x20   store8(doc, 91);\n\
                \x20   let mut i: i64 = 0;\n\
                \x20   while i < esc_len {\n\
                \x20       store8(doc + 1 + i, load8(esc_ptr + i));\n\
                \x20       i += 1;\n\
                \x20   }\n\
                \x20   store8(doc + 1 + esc_len, 93);\n\
                \x20   return json::parse_index(doc, esc_len + 2, 0);";
    let nasty: &[u8] = b"he said \"hi\"\n\ttabs\\slashes\x01\x1F and \xF0\x9F\x98\x80 utf8";
    assert_eq!(run(body, nasty), Ok(nasty.to_vec()));
    let empty: &[u8] = b"";
    assert_eq!(run(body, empty), Ok(empty.to_vec()));
}
