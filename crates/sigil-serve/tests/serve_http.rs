//! End-to-end HTTP trigger tests: real TCP requests against a spawned
//! server, real ephemeral tool executions behind the routes.

mod common;

use std::sync::Arc;
use std::time::Duration;

use common::{
    COUNTER_TOOL, ECHO_TOOL, TempDir, body_echo_tool, dispatcher_tool, envelope_echo_tool,
    failing_tool, http_get, http_post, http_request, http_request_full, json_escaped_path,
    method_header_tool, quote_header_tool, raw_bytes_tool, static_enveloped_tool, write_service,
};
use sigil_serve::config::Config;
use sigil_serve::host::ToolHost;
use sigil_serve::http;

/// Boot a service from a config string; returns the running server
/// (shut it down!) plus the scratch dir keeping the files alive.
fn boot(label: &str, config_json: &str, tools: &[(&str, &str)]) -> (http::HttpServer, TempDir) {
    let dir = TempDir::new(label);
    let config_path = write_service(dir.path(), config_json, tools);
    let (config, base_dir) = Config::load(&config_path).expect("config should load");
    let host = Arc::new(ToolHost::from_config(&config, &base_dir).expect("tools should compile"));
    let server =
        http::start(config.http.as_ref().expect("http configured"), host).expect("server starts");
    (server, dir)
}

const ECHO_CONFIG: &str = r#"{
  "tools": { "echo": { "source": "echo.sigil" } },
  "http": { "bind": "127.0.0.1:0", "routes": [ { "path": "/echo", "tool": "echo" } ] }
}"#;

#[test]
fn echo_route_roundtrips_body_and_query() {
    let (server, _dir) = boot("echo", ECHO_CONFIG, &[("echo.sigil", ECHO_TOOL)]);

    let (status, body) = http_post(server.tcp_addr(), "/echo", b"hello ephemeral world");
    assert_eq!(
        (status, body.as_slice()),
        (200, b"hello ephemeral world".as_slice())
    );

    // Bodyless request: the query string is the tool input.
    let (status, body) = http_get(server.tcp_addr(), "/echo?fmt=json&n=3");
    assert_eq!((status, body.as_slice()), (200, b"fmt=json&n=3".as_slice()));

    // Bodyless, queryless: empty input, empty output.
    let (status, body) = http_get(server.tcp_addr(), "/echo");
    assert_eq!((status, body.as_slice()), (200, b"".as_slice()));

    server.shutdown();
}

#[test]
fn unknown_route_is_404() {
    let (server, _dir) = boot("route404", ECHO_CONFIG, &[("echo.sigil", ECHO_TOOL)]);
    let (status, _) = http_get(server.tcp_addr(), "/nope");
    assert_eq!(status, 404);
    server.shutdown();
}

#[test]
fn tool_error_codes_map_to_http_statuses() {
    let config = r#"{
  "tools": {
    "missing": { "source": "missing.sigil" },
    "denied": { "source": "denied.sigil" },
    "weird": { "source": "weird.sigil" }
  },
  "http": { "bind": "127.0.0.1:0", "routes": [
    { "path": "/missing", "tool": "missing" },
    { "path": "/denied", "tool": "denied" },
    { "path": "/weird", "tool": "weird" }
  ] }
}"#;
    let missing = failing_tool(-404);
    let denied = failing_tool(-403);
    let weird = failing_tool(-777);
    let (server, _dir) = boot(
        "status_map",
        config,
        &[
            ("missing.sigil", &missing),
            ("denied.sigil", &denied),
            ("weird.sigil", &weird),
        ],
    );

    assert_eq!(http_get(server.tcp_addr(), "/missing").0, 404);
    assert_eq!(http_get(server.tcp_addr(), "/denied").0, 403);
    // Unrecognized tool codes refuse to invent semantics: 500.
    assert_eq!(http_get(server.tcp_addr(), "/weird").0, 500);
    server.shutdown();
}

#[test]
fn tool_status_passthrough_range() {
    // Any code in [-599, -400] passes through as that status; outside
    // the range gets 500.
    let config = r#"{
  "tools": {
    "m405": { "source": "m405.sigil" },
    "s503": { "source": "s503.sigil" },
    "low": { "source": "low.sigil" }
  },
  "http": { "bind": "127.0.0.1:0", "routes": [
    { "path": "/m405", "tool": "m405" },
    { "path": "/s503", "tool": "s503" },
    { "path": "/low", "tool": "low" }
  ] }
}"#;
    let m405 = failing_tool(-405);
    let s503 = failing_tool(-503);
    let low = failing_tool(-399);
    let (server, _dir) = boot(
        "status_range",
        config,
        &[
            ("m405.sigil", &m405),
            ("s503.sigil", &s503),
            ("low.sigil", &low),
        ],
    );
    assert_eq!(http_get(server.tcp_addr(), "/m405").0, 405);
    assert_eq!(http_get(server.tcp_addr(), "/s503").0, 503);
    assert_eq!(http_get(server.tcp_addr(), "/low").0, 500);
    server.shutdown();
}

// ─── Request envelope ───────────────────────────────────────────────────

const ENVELOPE_ECHO_CONFIG: &str = r#"{
  "tools": { "env": { "source": "env.sigil" } },
  "http": { "bind": "127.0.0.1:0", "routes": [
    { "path": "/env", "tool": "env", "input": "envelope" }
  ] }
}"#;

#[test]
fn envelope_carries_method_path_query_headers() {
    let tool = envelope_echo_tool();
    let (server, _dir) = boot("env_meta", ENVELOPE_ECHO_CONFIG, &[("env.sigil", &tool)]);

    let (status, body) = http_post(server.tcp_addr(), "/env?a=1&b=2", b"test-body");
    assert_eq!(status, 200);
    let envelope: serde_json::Value =
        serde_json::from_slice(&body).expect("tool returned the envelope JSON");
    assert_eq!(envelope["method"], "POST");
    assert_eq!(envelope["path"], "/env");
    assert_eq!(envelope["query"], "a=1&b=2");
    // Header names lowercased, values trimmed, arrival order kept —
    // exactly what the test client sent.
    assert_eq!(
        envelope["headers"],
        serde_json::json!([
            ["host", "test"],
            ["content-length", "9"],
            ["connection", "close"]
        ])
    );
    server.shutdown();
}

#[test]
fn envelope_body_tail_stays_binary_clean() {
    let tool = body_echo_tool();
    let (server, _dir) = boot("env_body", ENVELOPE_ECHO_CONFIG, &[("env.sigil", &tool)]);

    // Invalid UTF-8, NULs, CRLFs — the tail must come back byte-exact,
    // never re-encoded through the JSON.
    let payload: &[u8] = &[0x00, 0x9F, 0xFF, 0x0D, 0x0A, 0x22, 0x5C, 0x01, 0x80];
    let (status, body) = http_post(server.tcp_addr(), "/env", payload);
    assert_eq!(status, 200);
    assert_eq!(body, payload);

    // Bodyless request: empty tail (the query lives in the envelope).
    let (status, body) = http_get(server.tcp_addr(), "/env?q=only-in-envelope");
    assert_eq!(status, 200);
    assert_eq!(body, b"");
    server.shutdown();
}

// ─── Keep-alive ─────────────────────────────────────────────────────────

/// Read exactly one HTTP response (headers + Content-Length body) from
/// `stream`, returning (status, connection header, body).
///
/// `buf` CARRIES ACROSS CALLS and is the whole point of this signature. A
/// single `read` may return more than one response — under pipelining the
/// server can write response 2 before the client has consumed response 1,
/// and the kernel hands both over in one go. A helper that treated
/// everything-after-the-headers as the body would then see response 2's
/// bytes appended to response 1's, which is a HARNESS artifact, not a
/// server fault. So: consume exactly `header_end + 4 + content_length`
/// bytes and leave the remainder in `buf` for the next call.
fn read_one_response(
    stream: &mut std::net::TcpStream,
    buf: &mut Vec<u8>,
) -> (u16, String, Vec<u8>) {
    use std::io::Read;
    let header_end = loop {
        if let Some(pos) = buf.windows(4).position(|w| w == b"\r\n\r\n") {
            break pos;
        }
        let mut chunk = [0u8; 512];
        let n = stream.read(&mut chunk).expect("read response");
        assert!(n > 0, "connection closed mid-response");
        buf.extend_from_slice(&chunk[..n]);
    };
    let header_text = String::from_utf8_lossy(&buf[..header_end]).into_owned();
    let status: u16 = header_text
        .split(' ')
        .nth(1)
        .and_then(|s| s.parse().ok())
        .expect("status");
    let mut connection = String::new();
    let mut content_length = 0usize;
    for line in header_text.split("\r\n").skip(1) {
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        match name.trim().to_ascii_lowercase().as_str() {
            "connection" => connection = value.trim().to_ascii_lowercase(),
            "content-length" => content_length = value.trim().parse().expect("length"),
            _ => {}
        }
    }
    let body_start = header_end + 4;
    let response_end = body_start + content_length;
    while buf.len() < response_end {
        let mut chunk = vec![0u8; response_end - buf.len()];
        let n = stream.read(&mut chunk).expect("read body");
        assert!(n > 0, "connection closed mid-body");
        buf.extend_from_slice(&chunk[..n]);
    }
    let body = buf[body_start..response_end].to_vec();
    buf.drain(..response_end);
    (status, connection, body)
}

#[test]
fn keep_alive_serves_sequential_requests_on_one_connection() {
    use std::io::{Read, Write};
    let (server, _dir) = boot("keepalive_seq", ECHO_CONFIG, &[("echo.sigil", ECHO_TOOL)]);
    let mut stream = std::net::TcpStream::connect(server.tcp_addr()).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    // Leftover bytes carry across reads: a pipelined response 2 can arrive
    // inside response 1's read.
    let mut pending: Vec<u8> = Vec::new();

    for n in 0..3 {
        let body = format!("req-{n}");
        let head = format!(
            "POST /echo HTTP/1.1\r\nHost: t\r\nContent-Length: {}\r\n\r\n{body}",
            body.len()
        );
        stream.write_all(head.as_bytes()).unwrap();
        let (status, connection, got) = read_one_response(&mut stream, &mut pending);
        assert_eq!(status, 200);
        assert_eq!(connection, "keep-alive");
        assert_eq!(String::from_utf8_lossy(&got), body);
    }

    // Fourth request opts out; the server answers then hangs up.
    stream
        .write_all(b"GET /echo?done=1 HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
        .unwrap();
    let (status, connection, got) = read_one_response(&mut stream, &mut pending);
    assert_eq!((status, connection.as_str()), (200, "close"));
    assert_eq!(got, b"done=1");
    let mut end = [0u8; 1];
    assert_eq!(
        stream.read(&mut end).unwrap(),
        0,
        "server closed after Connection: close"
    );
    server.shutdown();
}

#[test]
fn pipelined_requests_are_not_dropped() {
    use std::io::Write;
    let (server, _dir) = boot("keepalive_pipe", ECHO_CONFIG, &[("echo.sigil", ECHO_TOOL)]);
    let mut stream = std::net::TcpStream::connect(server.tcp_addr()).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    // Leftover bytes carry across reads: a pipelined response 2 can arrive
    // inside response 1's read.
    let mut pending: Vec<u8> = Vec::new();

    // Both requests in ONE write: the second arrives inside the first
    // read and must survive in the leftover buffer.
    let combined = "POST /echo HTTP/1.1\r\nHost: t\r\nContent-Length: 5\r\n\r\nfirstPOST /echo HTTP/1.1\r\nHost: t\r\nContent-Length: 6\r\nConnection: close\r\n\r\nsecond";
    stream.write_all(combined.as_bytes()).unwrap();

    let (status, _, body) = read_one_response(&mut stream, &mut pending);
    assert_eq!((status, body.as_slice()), (200, b"first".as_slice()));
    let (status, connection, body) = read_one_response(&mut stream, &mut pending);
    assert_eq!((status, body.as_slice()), (200, b"second".as_slice()));
    assert_eq!(connection, "close");
    server.shutdown();
}

#[test]
fn http_1_0_closes_after_response() {
    use std::io::{Read, Write};
    let (server, _dir) = boot("keepalive_10", ECHO_CONFIG, &[("echo.sigil", ECHO_TOOL)]);
    let mut stream = std::net::TcpStream::connect(server.tcp_addr()).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    // Leftover bytes carry across reads: a pipelined response 2 can arrive
    // inside response 1's read.
    let mut pending: Vec<u8> = Vec::new();
    stream
        .write_all(b"GET /echo?old=1 HTTP/1.0\r\nHost: t\r\n\r\n")
        .unwrap();
    let (status, connection, body) = read_one_response(&mut stream, &mut pending);
    assert_eq!((status, connection.as_str()), (200, "close"));
    assert_eq!(body, b"old=1");
    let mut end = [0u8; 1];
    assert_eq!(stream.read(&mut end).unwrap(), 0, "HTTP/1.0 closes");
    server.shutdown();
}

#[test]
fn connection_request_cap_closes_at_one_hundred() {
    use std::io::{Read, Write};
    let (server, _dir) = boot("keepalive_cap", ECHO_CONFIG, &[("echo.sigil", ECHO_TOOL)]);
    let mut stream = std::net::TcpStream::connect(server.tcp_addr()).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    // Leftover bytes carry across reads: a pipelined response 2 can arrive
    // inside response 1's read.
    let mut pending: Vec<u8> = Vec::new();
    for n in 0..100 {
        let head = format!("GET /echo?n={n} HTTP/1.1\r\nHost: t\r\n\r\n");
        stream.write_all(head.as_bytes()).unwrap();
        let (status, connection, _) = read_one_response(&mut stream, &mut pending);
        assert_eq!(status, 200);
        let expected = if n == 99 { "close" } else { "keep-alive" };
        assert_eq!(connection, expected, "request #{n}");
    }
    let mut end = [0u8; 1];
    assert_eq!(
        stream.read(&mut end).unwrap(),
        0,
        "server rotates the connection"
    );
    server.shutdown();
}

// ─── Unix-socket bind ───────────────────────────────────────────────────

#[cfg(unix)]
#[test]
fn unix_socket_bind_serves_requests() {
    use std::io::{Read, Write};
    use std::os::unix::net::UnixStream;

    let dir = TempDir::new("uds");
    let sock = dir.path().join("serve.sock");
    let config = format!(
        r#"{{
  "tools": {{ "echo": {{ "source": "echo.sigil" }} }},
  "http": {{ "bind": "unix:{}", "routes": [ {{ "path": "/echo", "tool": "echo" }} ] }}
}}"#,
        json_escaped_path(&sock)
    );
    let config_path = write_service(dir.path(), &config, &[("echo.sigil", ECHO_TOOL)]);
    let (config, base_dir) = Config::load(&config_path).expect("config loads");
    let host = std::sync::Arc::new(ToolHost::from_config(&config, &base_dir).expect("compiles"));
    let server = http::start(config.http.as_ref().unwrap(), host).expect("uds server starts");

    let mut stream = UnixStream::connect(&sock).expect("connect over the socket");
    stream
        .write_all(b"GET /echo?over=unix HTTP/1.1\r\nHost: t\r\nConnection: close\r\n\r\n")
        .unwrap();
    let mut response = Vec::new();
    stream.read_to_end(&mut response).unwrap();
    let text = String::from_utf8_lossy(&response);
    assert!(text.starts_with("HTTP/1.1 200"), "got: {text}");
    assert!(text.ends_with("over=unix"), "got: {text}");

    server.shutdown();
    assert!(!sock.exists(), "socket file removed on shutdown");
}

// ─── Wildcard + parameter routing ───────────────────────────────────────

#[test]
fn route_precedence_literal_param_wildcard() {
    let config = r#"{
  "tools": {
    "a": { "source": "a.sigil" }, "b": { "source": "b.sigil" },
    "c": { "source": "c.sigil" }, "d": { "source": "d.sigil" }
  },
  "http": { "bind": "127.0.0.1:0", "routes": [
    { "path": "/a/b", "tool": "a" },
    { "path": "/a/:x", "tool": "b" },
    { "path": "/:y/b", "tool": "c" },
    { "path": "/a/*", "tool": "d" }
  ] }
}"#;
    let (ta, tb, tc, td) = (
        raw_bytes_tool(b"A"),
        raw_bytes_tool(b"B"),
        raw_bytes_tool(b"C"),
        raw_bytes_tool(b"D"),
    );
    let (server, _dir) = boot(
        "precedence",
        config,
        &[
            ("a.sigil", &ta),
            ("b.sigil", &tb),
            ("c.sigil", &tc),
            ("d.sigil", &td),
        ],
    );
    let body_of = |path: &str| {
        let (status, body) = http_get(server.tcp_addr(), path);
        assert_eq!(status, 200, "{path}");
        String::from_utf8(body).unwrap()
    };
    // Exact beats param beats wildcard, compared left-to-right.
    assert_eq!(body_of("/a/b"), "A");
    assert_eq!(body_of("/a/z"), "B");
    assert_eq!(body_of("/q/b"), "C");
    assert_eq!(body_of("/a/b/c"), "D");
    // No pattern reaches elsewhere.
    assert_eq!(http_get(server.tcp_addr(), "/q/z").0, 404);
    server.shutdown();
}

#[test]
fn params_flow_into_envelope() {
    let tool = envelope_echo_tool();
    let config = r#"{
  "tools": { "env": { "source": "env.sigil" } },
  "http": { "bind": "127.0.0.1:0", "routes": [
    { "path": "/things/:id/parts/*rest", "tool": "env", "input": "envelope" },
    { "path": "/files/*", "tool": "env", "input": "envelope" }
  ] }
}"#;
    let (server, _dir) = boot("env_params", config, &[("env.sigil", &tool)]);

    let (status, body) = http_get(server.tcp_addr(), "/things/42/parts/x/y.txt?q=1");
    assert_eq!(status, 200);
    let envelope: serde_json::Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(
        envelope["params"],
        serde_json::json!([["id", "42"], ["rest", "x/y.txt"]])
    );
    assert_eq!(envelope["path"], "/things/42/parts/x/y.txt");
    assert_eq!(envelope["query"], "q=1");

    // A bare `*` matches without binding anything.
    let (status, body) = http_get(server.tcp_addr(), "/files/deep/nested/name.bin");
    assert_eq!(status, 200);
    let envelope: serde_json::Value = serde_json::from_slice(&body).unwrap();
    assert_eq!(envelope["params"], serde_json::json!([]));
    server.shutdown();
}

#[test]
fn bad_route_patterns_rejected_at_boot() {
    let dir = TempDir::new("bad_patterns");
    std::fs::write(dir.path().join("echo.sigil"), ECHO_TOOL).unwrap();
    let cases: &[(&str, &str)] = &[
        (r#"{ "path": "/a/*/b", "tool": "echo" }"#, "final segment"),
        (r#"{ "path": "/a/:", "tool": "echo" }"#, "needs a name"),
        (
            r#"{ "path": "/t/:a", "tool": "echo" }, { "path": "/t/:b", "tool": "echo" }"#,
            "same shape",
        ),
        (
            r#"{ "path": "/t/:a/:a", "tool": "echo" }"#,
            "duplicate parameter",
        ),
    ];
    for (routes, fragment) in cases {
        let config = format!(
            r#"{{ "tools": {{ "echo": {{ "source": "echo.sigil" }} }},
                 "http": {{ "bind": "127.0.0.1:0", "routes": [ {routes} ] }} }}"#
        );
        let path = dir.path().join("bad.json");
        std::fs::write(&path, config).unwrap();
        let err = Config::load(&path).expect_err("pattern must be rejected");
        assert!(
            format!("{err:#}").contains(fragment),
            "case {routes:?}: expected `{fragment}` in: {err:#}"
        );
    }
}

// ─── Response envelope ──────────────────────────────────────────────────

const OUT_ENVELOPE_CONFIG: &str = r#"{
  "tools": { "t": { "source": "t.sigil" } },
  "http": { "bind": "127.0.0.1:0", "routes": [
    { "path": "/t", "tool": "t", "output": "envelope", "content_type": "text/x-default" }
  ] }
}"#;

fn header_value<'h>(headers: &'h [(String, String)], name: &str) -> Option<&'h str> {
    headers
        .iter()
        .find(|(n, _)| n == name)
        .map(|(_, v)| v.as_str())
}

#[test]
fn response_envelope_sets_status_headers_body() {
    let tool = static_enveloped_tool(
        r#"{"status":201,"headers":[["content-type","application/json"],["x-tool","sigil"]]}"#,
        br#"{"ok":true}"#,
    );
    let (server, _dir) = boot("resp_env", OUT_ENVELOPE_CONFIG, &[("t.sigil", &tool)]);

    let (status, headers, body) = http_request_full(server.tcp_addr(), "GET", "/t", b"");
    assert_eq!(status, 201);
    assert_eq!(
        header_value(&headers, "content-type"),
        Some("application/json")
    );
    assert_eq!(header_value(&headers, "x-tool"), Some("sigil"));
    // Host-owned framing headers are host-computed.
    assert_eq!(header_value(&headers, "content-length"), Some("11"));
    assert_eq!(header_value(&headers, "connection"), Some("close"));
    assert_eq!(body, br#"{"ok":true}"#);
    server.shutdown();
}

#[test]
fn response_envelope_defaults() {
    // {} is the minimal valid envelope: 200, route content_type.
    let tool = static_enveloped_tool("{}", b"plain body");
    let (server, _dir) = boot("resp_defaults", OUT_ENVELOPE_CONFIG, &[("t.sigil", &tool)]);
    let (status, headers, body) = http_request_full(server.tcp_addr(), "GET", "/t", b"");
    assert_eq!(status, 200);
    assert_eq!(
        header_value(&headers, "content-type"),
        Some("text/x-default")
    );
    assert_eq!(body, b"plain body");
    server.shutdown();

    let tool = static_enveloped_tool(r#"{"status":503}"#, b"");
    let (server, _dir) = boot(
        "resp_status_only",
        OUT_ENVELOPE_CONFIG,
        &[("t.sigil", &tool)],
    );
    assert_eq!(
        http_request_full(server.tcp_addr(), "GET", "/t", b"").0,
        503
    );
    server.shutdown();
}

#[test]
fn response_envelope_rejects_protocol_breakers() {
    // Every way a tool could break the response protocol → loud 500
    // with the malformed-envelope marker, never a passed-through
    // response.
    let cases: Vec<(&str, String)> = vec![
        ("short_frame", raw_bytes_tool(b"1234")),
        ("bad_digits", raw_bytes_tool(b"ABCDEFGH{}")),
        ("overrun", raw_bytes_tool(b"00000099{}")),
        ("bad_json", static_enveloped_tool("not json", b"")),
        ("not_object", static_enveloped_tool("[1,2]", b"")),
        (
            "unknown_field",
            static_enveloped_tool(r#"{"stauts":200}"#, b""),
        ),
        ("status_low", static_enveloped_tool(r#"{"status":99}"#, b"")),
        (
            "status_high",
            static_enveloped_tool(r#"{"status":600}"#, b""),
        ),
        (
            "forbidden_header",
            static_enveloped_tool(r#"{"headers":[["content-length","1"]]}"#, b""),
        ),
        (
            "transfer_encoding",
            static_enveloped_tool(r#"{"headers":[["transfer-encoding","chunked"]]}"#, b""),
        ),
        (
            "crlf_injection",
            static_enveloped_tool(
                "{\"headers\":[[\"x-a\",\"v\\r\\nSet-Cookie: pwned\"]]}",
                b"",
            ),
        ),
        (
            "bad_header_name",
            static_enveloped_tool(r#"{"headers":[["x a","v"]]}"#, b""),
        ),
        (
            "body_on_204",
            static_enveloped_tool(r#"{"status":204}"#, b"illegal"),
        ),
    ];
    for (label, tool) in &cases {
        let (server, _dir) = boot(
            &format!("resp_reject_{label}"),
            OUT_ENVELOPE_CONFIG,
            &[("t.sigil", tool)],
        );
        let (status, _headers, body) = http_request_full(server.tcp_addr(), "GET", "/t", b"");
        assert_eq!(status, 500, "case `{label}` must be rejected");
        assert!(
            String::from_utf8_lossy(&body).contains("malformed response envelope"),
            "case `{label}` body: {}",
            String::from_utf8_lossy(&body)
        );
        server.shutdown();
    }

    // And 204 with an EMPTY body is legal.
    let tool = static_enveloped_tool(r#"{"status":204}"#, b"");
    let (server, _dir) = boot("resp_204_ok", OUT_ENVELOPE_CONFIG, &[("t.sigil", &tool)]);
    let (status, _, body) = http_request_full(server.tcp_addr(), "GET", "/t", b"");
    assert_eq!((status, body.len()), (204, 0));
    server.shutdown();
}

#[test]
fn response_envelope_negative_codes_still_pass_through() {
    let tool = failing_tool(-404);
    let (server, _dir) = boot("resp_neg", OUT_ENVELOPE_CONFIG, &[("t.sigil", &tool)]);
    assert_eq!(
        http_request_full(server.tcp_addr(), "GET", "/t", b"").0,
        404
    );
    server.shutdown();
}

#[test]
fn guest_builds_envelope_with_escape_string() {
    // The encode side in-guest: the tool JSON-escapes the request
    // bytes into a response header value.
    let tool = quote_header_tool();
    let (server, _dir) = boot("resp_guest", OUT_ENVELOPE_CONFIG, &[("t.sigil", &tool)]);
    let (status, headers, body) =
        http_request_full(server.tcp_addr(), "POST", "/t", br#"he said "hi"	tab"#);
    assert_eq!(status, 201);
    assert_eq!(
        header_value(&headers, "x-quote"),
        Some("he said \"hi\"\ttab"),
        "escapes decoded by the host, tab survives"
    );
    assert_eq!(body, b"");
    server.shutdown();
}

#[test]
fn both_envelopes_roundtrip_method_into_header() {
    let tool = method_header_tool();
    let config = r#"{
  "tools": { "t": { "source": "t.sigil" } },
  "http": { "bind": "127.0.0.1:0", "routes": [
    { "path": "/t", "tool": "t", "input": "envelope", "output": "envelope" }
  ] }
}"#;
    let (server, _dir) = boot("both_env", config, &[("t.sigil", &tool)]);
    let (status, headers, _body) = http_request_full(server.tcp_addr(), "DELETE", "/t", b"");
    assert_eq!(status, 200);
    assert_eq!(header_value(&headers, "x-method"), Some("DELETE"));
    server.shutdown();
}

#[test]
fn dispatcher_tool_routes_on_method_via_json_codec() {
    // The point of the envelope: an in-guest dispatcher, parsing the
    // envelope with the stdlib json codec.
    let tool = dispatcher_tool();
    let config = r#"{
  "tools": { "api": { "source": "api.sigil" } },
  "http": { "bind": "127.0.0.1:0", "routes": [
    { "path": "/api", "tool": "api", "input": "envelope" }
  ] }
}"#;
    let (server, _dir) = boot("dispatch", config, &[("api.sigil", &tool)]);

    // GET → the tool extracts and returns the decoded query field.
    let (status, body) = http_get(server.tcp_addr(), "/api?who=world");
    assert_eq!((status, body.as_slice()), (200, b"who=world".as_slice()));

    // DELETE → the tool answers -405, the host maps it to HTTP 405.
    let (status, _) = http_request(server.tcp_addr(), "DELETE", "/api", b"");
    assert_eq!(status, 405);

    // POST → the tool echoes the raw body tail.
    let (status, body) = http_post(server.tcp_addr(), "/api", b"posted payload");
    assert_eq!(
        (status, body.as_slice()),
        (200, b"posted payload".as_slice())
    );
    server.shutdown();
}

#[test]
fn counter_route_increments_across_requests() {
    // The FaaS shape end-to-end: every request is a fresh ephemeral
    // run; continuity lives in the kv grant.
    let dir = TempDir::new("http_counter");
    let kv_dir = dir.path().join("kvdata");
    std::fs::create_dir_all(&kv_dir).unwrap();
    let config = format!(
        r#"{{
  "host_profile": "ephemeral",
  "tools": {{ "counter": {{ "source": "counter.sigil", "grants": {{
    "kv": ["demo={kv}"], "kv_write": ["demo={kv}"] }} }} }},
  "http": {{ "bind": "127.0.0.1:0", "routes": [ {{ "path": "/counter", "tool": "counter" }} ] }}
}}"#,
        kv = json_escaped_path(&kv_dir)
    );
    let config_path = write_service(dir.path(), &config, &[("counter.sigil", COUNTER_TOOL)]);
    let (config, base_dir) = Config::load(&config_path).expect("config loads");
    let host = Arc::new(ToolHost::from_config(&config, &base_dir).expect("compiles"));
    let server = http::start(config.http.as_ref().unwrap(), host).expect("server starts");

    for expected in ["1", "2", "3"] {
        let (status, body) = http_get(server.tcp_addr(), "/counter");
        assert_eq!(status, 200);
        assert_eq!(String::from_utf8_lossy(&body), expected);
    }
    server.shutdown();
}

#[test]
fn oversized_body_is_413_and_header_flood_431() {
    let (server, _dir) = boot("caps", ECHO_CONFIG, &[("echo.sigil", ECHO_TOOL)]);

    // Declared 5MB+1 body: rejected on Content-Length before transfer.
    use std::io::{Read, Write};
    let mut stream = std::net::TcpStream::connect(server.tcp_addr()).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    let head = format!(
        "POST /echo HTTP/1.1\r\nHost: t\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        5 * 1024 * 1024 + 1
    );
    stream.write_all(head.as_bytes()).unwrap();
    let mut response = Vec::new();
    let _ = stream.read_to_end(&mut response);
    let text = String::from_utf8_lossy(&response);
    assert!(
        text.starts_with("HTTP/1.1 413"),
        "expected 413, got: {}",
        text.lines().next().unwrap_or("")
    );

    // >8KB of headers: 431.
    let mut stream = std::net::TcpStream::connect(server.tcp_addr()).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .unwrap();
    stream
        .write_all(b"GET /echo HTTP/1.1\r\nHost: t\r\n")
        .unwrap();
    let filler = format!("X-Filler: {}\r\n", "y".repeat(1024));
    for _ in 0..10 {
        if stream.write_all(filler.as_bytes()).is_err() {
            break; // server may already have responded and closed
        }
    }
    let mut response = Vec::new();
    let _ = stream.read_to_end(&mut response);
    let text = String::from_utf8_lossy(&response);
    assert!(
        text.starts_with("HTTP/1.1 431"),
        "expected 431, got: {}",
        text.lines().next().unwrap_or("")
    );
    server.shutdown();
}

#[test]
fn concurrent_requests_all_succeed() {
    let (server, _dir) = boot("concurrent", ECHO_CONFIG, &[("echo.sigil", ECHO_TOOL)]);
    let addr = server.tcp_addr();
    let handles: Vec<_> = (0..8)
        .map(|n| {
            std::thread::spawn(move || {
                let payload = format!("payload-{n}");
                let (status, body) = http_post(addr, "/echo", payload.as_bytes());
                assert_eq!(status, 200);
                assert_eq!(String::from_utf8_lossy(&body), payload);
            })
        })
        .collect();
    for handle in handles {
        handle.join().expect("request thread");
    }
    server.shutdown();
}

#[test]
fn config_validation_rejects_bad_configs() {
    let dir = TempDir::new("bad_config");
    std::fs::write(dir.path().join("echo.sigil"), ECHO_TOOL).unwrap();

    let cases: &[(&str, &str)] = &[
        (
            r#"{ "tools": { "echo": { "source": "echo.sigil" } },
                "http": { "bind": "127.0.0.1:0",
                          "routes": [ { "path": "/a", "tool": "ghost" } ] } }"#,
            "unknown tool",
        ),
        (
            r#"{ "tools": { "echo": { "source": "echo.sigil" } },
                "http": { "bind": "127.0.0.1:0",
                          "routes": [ { "path": "no-slash", "tool": "echo" } ] } }"#,
            "must start with",
        ),
        (
            r#"{ "tools": { "echo": { "source": "echo.sigil" } },
                "schedule": [ { "name": "t", "tool": "echo", "every_ms": 1000 } ] }"#,
            "state_dir",
        ),
        (
            r#"{ "tools": { "echo": { "source": "echo.sigil" } } }"#,
            "nothing to serve",
        ),
    ];
    for (config_json, expected_fragment) in cases {
        let path = dir.path().join("bad.json");
        std::fs::write(&path, config_json).unwrap();
        let err = Config::load(&path).expect_err("config must be rejected");
        let message = format!("{err:#}");
        assert!(
            message.contains(expected_fragment),
            "error for {config_json:?} should mention `{expected_fragment}`, got: {message}"
        );
    }

    // Malformed kv grant descriptors refuse to boot (not silently drop).
    let bad_grant = r#"{ "tools": { "echo": { "source": "echo.sigil",
        "grants": { "kv": ["no-equals-sign"] } } },
        "http": { "bind": "127.0.0.1:0", "routes": [ { "path": "/e", "tool": "echo" } ] } }"#;
    let path = dir.path().join("bad_grant.json");
    std::fs::write(&path, bad_grant).unwrap();
    let (config, base_dir) = Config::load(&path).expect("shape parses");
    let Err(err) = ToolHost::from_config(&config, &base_dir) else {
        panic!("malformed kv grant descriptor must be rejected at boot");
    };
    assert!(format!("{err:#}").contains("NAMESPACE=DIR"), "got: {err:#}");
}
