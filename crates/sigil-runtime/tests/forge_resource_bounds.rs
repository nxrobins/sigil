use std::{
    io::{Read, Write},
    net::TcpListener,
    thread,
    time::{Duration, Instant},
};

use sigil_runtime::{HttpMethod, IoGrants, NetGrant, ToolError, ToolResult, execute_ephemeral};

const FUEL: u64 = 1_000;

fn wasm(wat_src: &str) -> Vec<u8> {
    wat::parse_str(wat_src).expect("test WAT should compile")
}

fn expect_trap(result: Result<ToolResult, ToolError>) -> String {
    match result {
        Err(ToolError::Trapped { message }) => message,
        other => panic!("expected trapped tool result, got {other:?}"),
    }
}

fn assert_tool_error_code(result: Result<ToolResult, ToolError>, code: u32) {
    let message = expect_trap(result);
    assert!(
        message.contains(&format!("tool returned error ({code})")),
        "expected tool error {code}, got `{message}`"
    );
}

#[test]
fn rejects_huge_guest_string_length_before_copying() {
    let module = wasm(
        r#"
        (module
          (import "ffi" "http_get" (func $http_get (param i32 i32) (result i64)))
          (memory (export "memory") 1)
          (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
          (func (export "tool__tool_main") (param i32 i32) (result i64)
            (call $http_get (i32.const 0) (i32.const 1048576))))
        "#,
    );

    assert_tool_error_code(
        execute_ephemeral(&module, b"", FUEL, &IoGrants::none()),
        413,
    );
}

#[test]
fn rejects_huge_guest_body_length_before_copying() {
    let module = wasm(
        r#"
        (module
          (import "ffi" "http_post" (func $http_post (param i32 i32 i32 i32) (result i64)))
          (memory (export "memory") 1)
          (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
          (data (i32.const 0) "http://127.0.0.1/")
          (func (export "tool__tool_main") (param i32 i32) (result i64)
            (call $http_post
              (i32.const 0)
              (i32.const 17)
              (i32.const 0)
              (i32.const 6291456))))
        "#,
    );
    let grants = IoGrants {
        net: vec![NetGrant {
            host_pattern: "127.0.0.1".into(),
            methods: vec![HttpMethod::Post],
        }],
        ..Default::default()
    };

    assert_tool_error_code(execute_ephemeral(&module, b"", FUEL, &grants), 413);
}

#[test]
fn rejects_huge_return_length_before_copying() {
    let module = wasm(
        r#"
        (module
          (memory (export "memory") 1)
          (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
          (func (export "tool__tool_main") (param i32 i32) (result i64)
            (i64.const 6291456)))
        "#,
    );

    let message = expect_trap(execute_ephemeral(&module, b"", FUEL, &IoGrants::none()));
    assert!(
        message.contains("tool output length exceeds forge limit"),
        "unexpected trap message: `{message}`"
    );
}

#[test]
fn rejects_alloc_i32_max_before_growing_guest_memory() {
    let module = wasm(
        r#"
        (module
          (import "sigil" "alloc" (func $alloc (param i32) (result i32)))
          (memory (export "memory") 1)
          (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
          (func (export "tool__tool_main") (param i32 i32) (result i64)
            (drop (call $alloc (i32.const 2147483647)))
            (i64.const 0)))
        "#,
    );

    expect_trap(execute_ephemeral(&module, b"", FUEL, &IoGrants::none()));
}

#[test]
fn blocking_http_get_times_out_instead_of_hanging() {
    let listener = TcpListener::bind("127.0.0.1:0").expect("loopback bind should succeed");
    let url = format!("http://{}/", listener.local_addr().expect("local addr"));
    let server = thread::spawn(move || {
        let (mut stream, _) = listener.accept().expect("server should accept one request");
        let mut buf = [0u8; 256];
        let _ = stream.read(&mut buf);
        let _ = stream.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 0\r\n");
        // Drip for ~8s: the promptness bound below must sit BETWEEN the
        // watchdog cut and a full read of this response, with real margin on
        // both sides, or the assert stops discriminating.
        for _ in 0..80 {
            if stream.write_all(b"x-test: slow\r\n").is_err() {
                return;
            }
            let _ = stream.flush();
            thread::sleep(Duration::from_millis(100));
        }
        let _ = stream.write_all(b"\r\n");
    });
    let module = wasm(
        r#"
        (module
          (import "ffi" "http_get" (func $http_get (param i32 i32) (result i64)))
          (memory (export "memory") 1)
          (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
          (func (export "tool__tool_main") (param i32 i32) (result i64)
            (call $http_get (local.get 0) (local.get 1))))
        "#,
    );
    let grants = IoGrants {
        net: vec![NetGrant {
            host_pattern: "127.0.0.1".into(),
            methods: vec![HttpMethod::Get],
        }],
        ..Default::default()
    };

    let started = Instant::now();
    assert_tool_error_code(
        execute_ephemeral(&module, url.as_bytes(), FUEL, &grants),
        502,
    );
    let elapsed = started.elapsed();
    server.join().expect("server thread should finish");

    // The shim's designed cut is HTTP_TOTAL_TIMEOUT (2s) plus its 500ms
    // watchdog grace; a 3s bound left ~500ms for scheduler jitter and a loaded
    // CI runner measured 3.09s. Five seconds keeps ~2.5s of jitter room while
    // staying far under the ~8s a fail-open full read of the drip would take.
    assert!(
        elapsed < Duration::from_secs(5),
        "HTTP shim should time out promptly; elapsed {elapsed:?}"
    );
}

/// The watchdog bound is PER PHASE (one window per redirect hop + one for the
/// body read), matching the fresh ureq global timer each hop gets — NOT one
/// window for the whole call. Pin that: a redirect chain whose TOTAL time
/// exceeds one watchdog window, but whose individual hops each clear it
/// comfortably, must still succeed. A regression to a whole-call bound turns
/// this deterministic success into a 502 at ~2.5s.
#[test]
fn redirect_chain_slower_than_one_watchdog_window_still_succeeds() {
    let listener = TcpListener::bind("127.0.0.1:0").expect("loopback bind should succeed");
    let addr = listener.local_addr().expect("local addr");
    let url = format!("http://{addr}/");
    let server = thread::spawn(move || {
        // Hop 1: after ~1.4s, a 301 to the same (granted) host. Connection:
        // close forces the follow-up hop onto a fresh connection so this
        // server can serve it from a second accept().
        let (mut stream, _) = listener.accept().expect("accept hop 1");
        let mut buf = [0u8; 512];
        let _ = stream.read(&mut buf);
        thread::sleep(Duration::from_millis(1_400));
        let redirect = format!(
            "HTTP/1.1 301 Moved Permanently\r\nLocation: http://{addr}/moved\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
        );
        stream
            .write_all(redirect.as_bytes())
            .expect("write 301 response");
        let _ = stream.flush();
        drop(stream);
        // Hop 2: after another ~1.4s, the final 200. Total ≈2.8s — past one
        // 2.5s watchdog window, but each hop well inside its own.
        let (mut stream, _) = listener.accept().expect("accept hop 2");
        let _ = stream.read(&mut buf);
        thread::sleep(Duration::from_millis(1_400));
        stream
            .write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nConnection: close\r\n\r\nok")
            .expect("write 200 response");
        let _ = stream.flush();
    });
    let module = wasm(
        r#"
        (module
          (import "ffi" "http_get" (func $http_get (param i32 i32) (result i64)))
          (memory (export "memory") 1)
          (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
          (func (export "tool__tool_main") (param i32 i32) (result i64)
            (call $http_get (local.get 0) (local.get 1))))
        "#,
    );
    let grants = IoGrants {
        net: vec![NetGrant {
            host_pattern: "127.0.0.1".into(),
            methods: vec![HttpMethod::Get],
        }],
        ..Default::default()
    };

    let started = Instant::now();
    let result = execute_ephemeral(&module, url.as_bytes(), FUEL, &grants)
        .expect("slow-but-honest redirect chain must not trip the per-hop watchdog");
    let elapsed = started.elapsed();
    server.join().expect("server thread should finish");

    assert_eq!(
        result.output, b"ok",
        "final hop body should reach the guest"
    );
    assert!(
        elapsed > Duration::from_millis(2_600),
        "the chain must actually outlast one watchdog window; elapsed {elapsed:?}"
    );
    assert!(
        elapsed < Duration::from_secs(6),
        "the chain must still finish promptly; elapsed {elapsed:?}"
    );
}
