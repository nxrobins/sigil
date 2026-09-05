//! Shared helpers for sigil-serve integration tests: scratch dirs,
//! inline tool sources, a config writer, and a tiny HTTP/1.1 client.
//!
//! Each integration-test binary compiles this module separately, so
//! any one binary uses only a subset of it.
#![allow(dead_code)]

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpStream};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

/// Fresh scratch directory, best-effort removed on drop.
pub struct TempDir(pub PathBuf);

impl TempDir {
    pub fn new(label: &str) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "sigil_serve_{label}_{}_{:x}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).expect("create scratch dir");
        Self(dir)
    }
    pub fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Echo tool: output = input bytes.
pub const ECHO_TOOL: &str = "module tool;\n\
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
    let out_ptr: i64 = alloc(input_len);\n\
    let mut i: i64 = 0;\n\
    while i < input_len {\n\
        store8(out_ptr + i, load8(input_ptr + i));\n\
        i += 1;\n\
    }\n\
    return out_ptr << 32 | input_len;\n\
}\n";

/// Always fails with the given negative code.
pub fn failing_tool(code: i64) -> String {
    format!(
        "module tool;\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n\
             let rc: i64 = {code};\n\
             return rc;\n\
         }}\n"
    )
}

/// The kv counter: loads, increments, persists, prints. Namespace
/// `demo`, key `count` — state crosses runs through the kv grant.
pub const COUNTER_TOOL: &str = "#[ring(outer)] #[trusted] module tool;\n\
extern \"C\" fn kv_get(ns: i32, ns_len: i32, key: i32, key_len: i32) -> i64 ! { FFI, Unsafe };\n\
extern \"C\" fn kv_put(ns: i32, ns_len: i32, key: i32, key_len: i32, val: i32, val_len: i32) -> i64 ! { FFI, Unsafe };\n\
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc, FFI, Unsafe } {\n\
    let ns_buf: i64 = alloc(4);\n\
    store8(ns_buf, 100);\n\
    store8(ns_buf + 1, 101);\n\
    store8(ns_buf + 2, 109);\n\
    store8(ns_buf + 3, 111);\n\
    let ns_ptr: i32 = ns_buf.as_i32();\n\
    let key_buf: i64 = alloc(5);\n\
    store8(key_buf, 99);\n\
    store8(key_buf + 1, 111);\n\
    store8(key_buf + 2, 117);\n\
    store8(key_buf + 3, 110);\n\
    store8(key_buf + 4, 116);\n\
    let key_ptr: i32 = key_buf.as_i32();\n\
    let not_found: i64 = -404;\n\
    let got: i64 @Internal = kv_get(ns_ptr, 4, key_ptr, 5);\n\
    let mut n: i64 @Internal = 0;\n\
    if got == not_found {\n\
        n = 0;\n\
    } else {\n\
        if got < 0 {\n\
            return got;\n\
        } else {\n\
            let vptr: i64 @Internal = got >> 32;\n\
            let vlen: i64 @Internal = got & 0xFFFFFFFF;\n\
            let mut i: i64 @Internal = 0;\n\
            while i < vlen {\n\
                n = n * 10 + load8(vptr + i) - 48;\n\
                i += 1;\n\
            }\n\
        }\n\
    }\n\
    n += 1;\n\
    let mut digits: i64 @Internal = 1;\n\
    let mut probe: i64 @Internal = n;\n\
    while probe > 9 {\n\
        probe = probe / 10;\n\
        digits += 1;\n\
    }\n\
    let out: i64 @Internal = alloc(digits);\n\
    let mut pos: i64 @Internal = digits - 1;\n\
    let mut rem: i64 @Internal = n;\n\
    while pos >= 0 {\n\
        store8(out + pos, 48 + rem % 10);\n\
        rem = rem / 10;\n\
        pos -= 1;\n\
    }\n\
    let val_ptr: i32 @Internal = out.as_i32();\n\
    let val_len: i32 @Internal = digits.as_i32();\n\
    let put_rc: i64 @Internal = kv_put(ns_ptr, 4, key_ptr, 5, val_ptr, val_len);\n\
    if put_rc < 0 {\n\
        return put_rc;\n\
    } else {\n\
    }\n\
    return out << 32 | digits;\n\
}\n";

/// The real stdlib json module source, for composing into tools that
/// `use sigil::json;` (tool first, stdlib appended — compose.py order).
pub fn stdlib_json_source() -> String {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("..");
    p.push("..");
    p.push("stdlib");
    p.push("sigil");
    p.push("json.sigil");
    std::fs::read_to_string(&p).expect("read stdlib/sigil/json.sigil")
}

/// Shared preamble for envelope-consuming tools: parses the 8-digit
/// ASCII frame into `env_len` (bailing -400 on malformed frames) and
/// leaves `env_ptr` at the envelope JSON.
pub const FRAME_PREAMBLE: &str = "    if input_len < 8 {\n        return -400;\n    } else {\n    }\n\
\x20   let mut env_len: i64 = 0;\n\
\x20   let mut fi: i64 = 0;\n\
\x20   while fi < 8 {\n\
\x20       let d: i64 = load8(input_ptr + fi);\n\
\x20       if d < 48 {\n            return -400;\n        } else {\n        }\n\
\x20       if d > 57 {\n            return -400;\n        } else {\n        }\n\
\x20       env_len = env_len * 10 + d - 48;\n\
\x20       fi += 1;\n\
\x20   }\n\
\x20   if 8 + env_len > input_len {\n        return -400;\n    } else {\n    }\n\
\x20   let env_ptr: i64 = input_ptr + 8;\n";

/// Envelope-echo: returns the envelope JSON slice (copied out).
pub fn envelope_echo_tool() -> String {
    format!(
        "module tool;\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         {FRAME_PREAMBLE}\
         \x20   let out: i64 = alloc(env_len);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < env_len {{\n\
         \x20       store8(out + i, load8(env_ptr + i));\n\
         \x20       i += 1;\n\
         \x20   }}\n\
         \x20   return out << 32 | env_len;\n\
         }}\n"
    )
}

/// Body-echo: returns the raw body tail after the envelope, untouched.
pub fn body_echo_tool() -> String {
    format!(
        "module tool;\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         {FRAME_PREAMBLE}\
         \x20   let body_start: i64 = 8 + env_len;\n\
         \x20   let body_len: i64 = input_len - body_start;\n\
         \x20   let out: i64 = alloc(body_len);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < body_len {{\n\
         \x20       store8(out + i, load8(input_ptr + body_start + i));\n\
         \x20       i += 1;\n\
         \x20   }}\n\
         \x20   return out << 32 | body_len;\n\
         }}\n"
    )
}

/// The flagship dispatcher: extracts "method" from the envelope with
/// the stdlib json codec, answers DELETE with -405 (⇒ HTTP 405),
/// echoes the decoded query on GET, and echoes the body tail
/// otherwise. Composed with the real stdlib json source.
pub fn dispatcher_tool() -> String {
    let tool = format!(
        "module tool;\n\n\
         use sigil::json;\n\n\
         fn is_get(p: i64, len: i64) -> i64 {{\n\
         \x20   if len == 3 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   if load8(p) == 71 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   if load8(p + 1) == 69 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   if load8(p + 2) == 84 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   return 1;\n\
         }}\n\n\
         fn is_delete(p: i64, len: i64) -> i64 {{\n\
         \x20   if len == 6 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   if load8(p) == 68 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   if load8(p + 1) == 69 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   if load8(p + 2) == 76 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   if load8(p + 3) == 69 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   if load8(p + 4) == 84 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   if load8(p + 5) == 69 {{\n    }} else {{\n        return 0;\n    }}\n\
         \x20   return 1;\n\
         }}\n\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         {FRAME_PREAMBLE}\
         \x20   let mkey: i64 = alloc(6);\n\
         \x20   store8(mkey, 109);\n\
         \x20   store8(mkey + 1, 101);\n\
         \x20   store8(mkey + 2, 116);\n\
         \x20   store8(mkey + 3, 104);\n\
         \x20   store8(mkey + 4, 111);\n\
         \x20   store8(mkey + 5, 100);\n\
         \x20   let m: i64 = json::parse_field(env_ptr, env_len, mkey, 6);\n\
         \x20   if m < 0 {{\n        return m;\n    }} else {{\n    }}\n\
         \x20   let m_ptr: i64 = m >> 32;\n\
         \x20   let m_len: i64 = m & 0xFFFFFFFF;\n\
         \x20   if is_delete(m_ptr, m_len) == 1 {{\n\
         \x20       return -405;\n\
         \x20   }} else {{\n    }}\n\
         \x20   if is_get(m_ptr, m_len) == 1 {{\n\
         \x20       let qkey: i64 = alloc(5);\n\
         \x20       store8(qkey, 113);\n\
         \x20       store8(qkey + 1, 117);\n\
         \x20       store8(qkey + 2, 101);\n\
         \x20       store8(qkey + 3, 114);\n\
         \x20       store8(qkey + 4, 121);\n\
         \x20       return json::parse_field(env_ptr, env_len, qkey, 5);\n\
         \x20   }} else {{\n    }}\n\
         \x20   let body_start: i64 = 8 + env_len;\n\
         \x20   let body_len: i64 = input_len - body_start;\n\
         \x20   let out: i64 = alloc(body_len);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < body_len {{\n\
         \x20       store8(out + i, load8(input_ptr + body_start + i));\n\
         \x20       i += 1;\n\
         \x20   }}\n\
         \x20   return out << 32 | body_len;\n\
         }}\n"
    );
    format!("{tool}\n{}", stdlib_json_source())
}

/// Emit `store8({base} + i, b);` lines for a byte literal.
fn stores_at(base: &str, bytes: &[u8]) -> String {
    let mut out = String::new();
    for (i, b) in bytes.iter().enumerate() {
        out.push_str(&format!("    store8({base} + {i}, {b});\n"));
    }
    out
}

/// Tool that outputs exactly `bytes`, whatever the input.
pub fn raw_bytes_tool(bytes: &[u8]) -> String {
    let n = bytes.len().max(1);
    format!(
        "module tool;\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         \x20   let out: i64 = alloc({n});\n\
         {}\
         \x20   return out << 32 | {};\n\
         }}\n",
        stores_at("out", bytes),
        bytes.len()
    )
}

/// Tool that outputs a well-formed response frame with the given
/// envelope JSON and body baked in.
pub fn static_enveloped_tool(envelope_json: &str, body: &[u8]) -> String {
    let mut bytes = format!("{:08}", envelope_json.len()).into_bytes();
    bytes.extend_from_slice(envelope_json.as_bytes());
    bytes.extend_from_slice(body);
    raw_bytes_tool(&bytes)
}

/// Guest-BUILT response envelope: escapes the request bytes with
/// `json::escape_string` into an `x-quote` response header, status
/// 201, empty body. Composed with the real stdlib json source — the
/// encode-side counterpart of the dispatcher test.
pub fn quote_header_tool() -> String {
    let prefix: &[u8] = br#"{"headers":[["x-quote","#;
    let suffix: &[u8] = br#"]],"status":201}"#;
    let plen = prefix.len();
    let slen = suffix.len();
    let tool = format!(
        "module tool;\n\n\
         use sigil::json;\n\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         \x20   let esc: i64 = json::escape_string(input_ptr, input_len);\n\
         \x20   if esc < 0 {{\n        return esc;\n    }} else {{\n    }}\n\
         \x20   let esc_ptr: i64 = esc >> 32;\n\
         \x20   let esc_len: i64 = esc & 0xFFFFFFFF;\n\
         \x20   let env_len: i64 = {plen} + esc_len + {slen};\n\
         \x20   let total: i64 = 8 + env_len;\n\
         \x20   let out: i64 = alloc(total);\n\
         \x20   let mut w: i64 = 7;\n\
         \x20   let mut rem: i64 = env_len;\n\
         \x20   while w >= 0 {{\n\
         \x20       store8(out + w, 48 + rem % 10);\n\
         \x20       rem = rem / 10;\n\
         \x20       w -= 1;\n\
         \x20   }}\n\
         \x20   let p: i64 = out + 8;\n\
         {prefix_stores}\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < esc_len {{\n\
         \x20       store8(p + {plen} + i, load8(esc_ptr + i));\n\
         \x20       i += 1;\n\
         \x20   }}\n\
         \x20   let s: i64 = p + {plen} + esc_len;\n\
         {suffix_stores}\
         \x20   return out << 32 | total;\n\
         }}\n",
        prefix_stores = stores_at("p", prefix),
        suffix_stores = stores_at("s", suffix),
    );
    format!("{tool}\n{}", stdlib_json_source())
}

/// Both envelopes at once: parses the REQUEST envelope, extracts
/// "method" with `json::parse_field`, and answers with a RESPONSE
/// envelope carrying it in an `x-method` header (escaped via
/// `json::escape_string`), status 200, empty body.
pub fn method_header_tool() -> String {
    let prefix: &[u8] = br#"{"headers":[["x-method","#;
    let suffix: &[u8] = br#"]]}"#;
    let plen = prefix.len();
    let slen = suffix.len();
    let tool = format!(
        "module tool;\n\n\
         use sigil::json;\n\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         {FRAME_PREAMBLE}\
         \x20   let mkey: i64 = alloc(6);\n\
         \x20   store8(mkey, 109);\n\
         \x20   store8(mkey + 1, 101);\n\
         \x20   store8(mkey + 2, 116);\n\
         \x20   store8(mkey + 3, 104);\n\
         \x20   store8(mkey + 4, 111);\n\
         \x20   store8(mkey + 5, 100);\n\
         \x20   let m: i64 = json::parse_field(env_ptr, env_len, mkey, 6);\n\
         \x20   if m < 0 {{\n        return m;\n    }} else {{\n    }}\n\
         \x20   let m_ptr: i64 = m >> 32;\n\
         \x20   let m_len: i64 = m & 0xFFFFFFFF;\n\
         \x20   let esc: i64 = json::escape_string(m_ptr, m_len);\n\
         \x20   if esc < 0 {{\n        return esc;\n    }} else {{\n    }}\n\
         \x20   let esc_ptr: i64 = esc >> 32;\n\
         \x20   let esc_len: i64 = esc & 0xFFFFFFFF;\n\
         \x20   let renv_len: i64 = {plen} + esc_len + {slen};\n\
         \x20   let total: i64 = 8 + renv_len;\n\
         \x20   let out: i64 = alloc(total);\n\
         \x20   let mut w: i64 = 7;\n\
         \x20   let mut rem: i64 = renv_len;\n\
         \x20   while w >= 0 {{\n\
         \x20       store8(out + w, 48 + rem % 10);\n\
         \x20       rem = rem / 10;\n\
         \x20       w -= 1;\n\
         \x20   }}\n\
         \x20   let p: i64 = out + 8;\n\
         {prefix_stores}\
         \x20   let mut ci: i64 = 0;\n\
         \x20   while ci < esc_len {{\n\
         \x20       store8(p + {plen} + ci, load8(esc_ptr + ci));\n\
         \x20       ci += 1;\n\
         \x20   }}\n\
         \x20   let s: i64 = p + {plen} + esc_len;\n\
         {suffix_stores}\
         \x20   return out << 32 | total;\n\
         }}\n",
        prefix_stores = stores_at("p", prefix),
        suffix_stores = stores_at("s", suffix),
    );
    format!("{tool}\n{}", stdlib_json_source())
}

/// Full HTTP request: returns (status, response headers
/// (lowercased names), body).
pub fn http_request_full(
    addr: SocketAddr,
    method: &str,
    target: &str,
    body: &[u8],
) -> (u16, Vec<(String, String)>, Vec<u8>) {
    let mut stream = TcpStream::connect(addr).expect("connect");
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    let head = format!(
        "{method} {target} HTTP/1.1\r\nHost: test\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(head.as_bytes()).expect("write head");
    stream.write_all(body).expect("write body");
    stream.flush().unwrap();
    let mut response = Vec::new();
    stream.read_to_end(&mut response).expect("read response");
    parse_response_full(&response)
}

fn parse_response_full(raw: &[u8]) -> (u16, Vec<(String, String)>, Vec<u8>) {
    let header_end = raw
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("response has header terminator");
    let header_text = String::from_utf8_lossy(&raw[..header_end]).into_owned();
    let mut lines = header_text.split("\r\n");
    let status_line = lines.next().unwrap_or("");
    let status: u16 = status_line
        .split(' ')
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| panic!("bad status line: {status_line}"));
    if status == 100 {
        return parse_response_full(&raw[header_end + 4..]);
    }
    let headers = lines
        .filter_map(|line| line.split_once(':'))
        .map(|(name, value)| (name.trim().to_ascii_lowercase(), value.trim().to_owned()))
        .collect();
    (status, headers, raw[header_end + 4..].to_vec())
}

/// Write tool sources + a config file into `dir`; returns the config
/// path. `config_json` may reference tool files by bare name.
pub fn write_service(dir: &Path, config_json: &str, tools: &[(&str, &str)]) -> PathBuf {
    for (file_name, source) in tools {
        std::fs::write(dir.join(file_name), source).expect("write tool source");
    }
    let config_path = dir.join("service.json");
    std::fs::write(&config_path, config_json).expect("write config");
    config_path
}

/// A path escaped for interpolation *inside* a JSON string literal.
/// The quotes are the caller's, so the result can be prefixed
/// (`"demo={dir}"`) as well as used bare (`"{dir}"`).
///
/// Windows temp dirs are `C:\Users\...` and `\` is a JSON escape
/// character, so a raw path there yields a config that fails to parse
/// or — worse — decodes to a different path. CI is Linux-only and
/// never exercises that, hence `escaped_path_is_json_safe` below.
pub fn json_escaped_path(path: &Path) -> String {
    let quoted =
        serde_json::to_string(path.to_str().expect("utf-8 path")).expect("path serializes");
    quoted
        .strip_prefix('"')
        .and_then(|q| q.strip_suffix('"'))
        .expect("serde_json quotes strings")
        .to_owned()
}

/// Fences [`json_escaped_path`] on Linux too: the escaping is a no-op
/// for `/tmp/...`, so without this nothing on CI would notice it being
/// dropped again.
///
/// The fixture is a synthetic `Z:\scratch\...` rather than a real temp
/// dir: `test_ci_hygiene.py::test_tracked_text_has_no_developer_local_
/// paths` rejects any tracked file containing `<drive>:\Users\<name>\`,
/// and it cannot tell a fixture from a leaked path. Only the drive
/// letter, the separators, and the embedded quote matter here.
#[test]
fn escaped_path_is_json_safe() {
    let windowsy = Path::new(r#"Z:\scratch\a"b\tmp"#);
    let escaped = json_escaped_path(windowsy);
    assert_eq!(escaped, r#"Z:\\scratch\\a\"b\\tmp"#);
    // Round-trips through a real parse, in the prefixed shape the kv
    // grants use.
    let value: serde_json::Value =
        serde_json::from_str(&format!(r#""demo={escaped}""#)).expect("escaped path re-parses");
    assert_eq!(value.as_str().unwrap(), r#"demo=Z:\scratch\a"b\tmp"#);
    // Unix paths pass through untouched.
    assert_eq!(json_escaped_path(Path::new("/tmp/x")), "/tmp/x");
}

/// Minimal HTTP/1.1 request; returns (status, body).
pub fn http_request(addr: SocketAddr, method: &str, target: &str, body: &[u8]) -> (u16, Vec<u8>) {
    let mut stream = TcpStream::connect(addr).expect("connect");
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    let head = format!(
        "{method} {target} HTTP/1.1\r\nHost: test\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(head.as_bytes()).expect("write head");
    stream.write_all(body).expect("write body");
    stream.flush().unwrap();

    let mut response = Vec::new();
    stream.read_to_end(&mut response).expect("read response");
    parse_response(&response)
}

pub fn http_get(addr: SocketAddr, target: &str) -> (u16, Vec<u8>) {
    http_request(addr, "GET", target, b"")
}

pub fn http_post(addr: SocketAddr, target: &str, body: &[u8]) -> (u16, Vec<u8>) {
    http_request(addr, "POST", target, body)
}

fn parse_response(raw: &[u8]) -> (u16, Vec<u8>) {
    let header_end = raw
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .expect("response has header terminator");
    let header_text = String::from_utf8_lossy(&raw[..header_end]);
    let status_line = header_text.split("\r\n").next().unwrap_or("");
    let status: u16 = status_line
        .split(' ')
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| panic!("bad status line: {status_line}"));
    // 100-continue interim responses precede the real one.
    if status == 100 {
        return parse_response(&raw[header_end + 4..]);
    }
    (status, raw[header_end + 4..].to_vec())
}

/// Poll `condition` until it holds or `timeout` elapses.
pub fn wait_until(timeout: Duration, mut condition: impl FnMut() -> bool) -> bool {
    let deadline = Instant::now() + timeout;
    while Instant::now() < deadline {
        if condition() {
            return true;
        }
        std::thread::sleep(Duration::from_millis(25));
    }
    condition()
}

/// Read the single kv backing file in `kv_dir` as an ASCII integer
/// (the counter's persisted value). None when no key exists yet.
pub fn read_counter(kv_dir: &Path) -> Option<i64> {
    let entries = std::fs::read_dir(kv_dir).ok()?;
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) == Some("kv") {
            let text = std::fs::read_to_string(&path).ok()?;
            return text.trim().parse().ok();
        }
    }
    None
}
