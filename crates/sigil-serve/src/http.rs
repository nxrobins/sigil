//! The HTTP trigger: a minimal std-only HTTP/1.1 server that maps each
//! request to one ephemeral tool execution.
//!
//! The v1 request contract, kept deliberately small:
//! - routes match the request path EXACTLY (no wildcards);
//! - the tool's input bytes are the request body; for bodyless
//!   requests (GET et al.) they are the raw query string instead;
//! - the tool's output bytes are the 200 response body;
//! - the tool's negative error codes map straight onto HTTP statuses
//!   (-404 → 404, -403 → 403, -400 → 400, -413 → 413, -429 → 429,
//!   anything else → 500) — the stdlib's HTTP-shaped conventions
//!   were chosen for exactly this;
//! - every response is `Connection: close` (no keep-alive in v1).
//!
//! Bounded like the rest of the host surface: 8 KB header cap, 5 MB
//! body cap, per-connection read/write timeouts, and an in-flight
//! connection cap beyond which requests get an immediate 503.

use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Duration;

use anyhow::Context;

use crate::config::{HttpConfig, InputMode, OutputMode};
use crate::host::{ToolHost, ToolOutcome};

const MAX_HEADER_BYTES: usize = 8 * 1024;
const MAX_BODY_BYTES: usize = 5 * 1024 * 1024;
const IO_TIMEOUT: Duration = Duration::from_secs(5);
/// Requests served on one keep-alive connection before the host closes
/// it (resource rotation; the client simply reconnects).
const MAX_REQUESTS_PER_CONNECTION: usize = 100;

#[derive(Clone)]
struct RouteEntry {
    pattern: Vec<Segment>,
    tool: String,
    content_type: String,
    input: InputMode,
    output: OutputMode,
}

/// One compiled segment of a route pattern (validated at boot by
/// `config::validate_route_pattern`).
#[derive(Clone)]
enum Segment {
    Literal(String),
    Param(String),
    /// Final-position wildcard; binds the remaining path (possibly
    /// empty) under this name ("" for a bare `*`).
    Wild(String),
}

fn compile_pattern(pattern: &str) -> Vec<Segment> {
    pattern
        .strip_prefix('/')
        .unwrap_or(pattern)
        .split('/')
        .map(|segment| {
            if let Some(name) = segment.strip_prefix(':') {
                Segment::Param(name.to_owned())
            } else if let Some(name) = segment.strip_prefix('*') {
                Segment::Wild(name.to_owned())
            } else {
                Segment::Literal(segment.to_owned())
            }
        })
        .collect()
}

/// Match `path` against a compiled pattern; `Some(params)` on match.
fn match_pattern(pattern: &[Segment], path: &str) -> Option<Vec<(String, String)>> {
    let segments: Vec<&str> = path.strip_prefix('/').unwrap_or(path).split('/').collect();
    let mut params = Vec::new();
    let mut cursor = 0usize;
    for (index, segment) in pattern.iter().enumerate() {
        match segment {
            Segment::Literal(want) => {
                if segments.get(cursor) != Some(&want.as_str()) {
                    return None;
                }
                cursor += 1;
            }
            Segment::Param(name) => {
                let got = segments.get(cursor)?;
                if got.is_empty() {
                    return None;
                }
                params.push((name.clone(), (*got).to_owned()));
                cursor += 1;
            }
            Segment::Wild(name) => {
                debug_assert_eq!(index, pattern.len() - 1);
                let rest = segments[cursor.min(segments.len())..].join("/");
                if !name.is_empty() {
                    params.push((name.clone(), rest));
                }
                return Some(params);
            }
        }
    }
    if cursor == segments.len() {
        Some(params)
    } else {
        None
    }
}

/// Pick the most specific matching route: per-segment specificity
/// (literal 0 < param 1 < wildcard 2) compared left-to-right. Boot
/// validation guarantees no two routes share a shape, so no ties.
type RouteParams = Vec<(String, String)>;

fn match_route<'r>(routes: &'r [RouteEntry], path: &str) -> Option<(&'r RouteEntry, RouteParams)> {
    let mut best: Option<(Vec<u8>, &RouteEntry, RouteParams)> = None;
    for route in routes {
        let Some(params) = match_pattern(&route.pattern, path) else {
            continue;
        };
        let key: Vec<u8> = route
            .pattern
            .iter()
            .map(|segment| match segment {
                Segment::Literal(_) => 0,
                Segment::Param(_) => 1,
                Segment::Wild(_) => 2,
            })
            .collect();
        let better = match &best {
            None => true,
            Some((best_key, _, _)) => key < *best_key,
        };
        if better {
            best = Some((key, route, params));
        }
    }
    best.map(|(_, route, params)| (route, params))
}

/// Where a server ended up listening.
#[derive(Debug, Clone)]
pub enum Bound {
    Tcp(SocketAddr),
    /// Unix domain socket — the TLS-termination-friendly bind for a
    /// local reverse proxy; no TCP loopback exposure at all.
    Unix(PathBuf),
}

impl std::fmt::Display for Bound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bound::Tcp(addr) => write!(f, "{addr}"),
            Bound::Unix(path) => write!(f, "unix:{}", path.display()),
        }
    }
}

/// A running HTTP trigger. Dropping the handle does NOT stop the
/// server; call [`HttpServer::shutdown`].
pub struct HttpServer {
    pub bound: Bound,
    shutdown: Arc<AtomicBool>,
    accept_thread: Option<std::thread::JoinHandle<()>>,
}

impl HttpServer {
    /// The TCP address this server bound. Panics for unix-socket
    /// binds — test/tooling convenience for the common case.
    pub fn tcp_addr(&self) -> SocketAddr {
        match &self.bound {
            Bound::Tcp(addr) => *addr,
            Bound::Unix(path) => panic!("server is bound to unix:{}", path.display()),
        }
    }

    /// Signal the accept loop to stop and wait for it to exit.
    /// In-flight request threads are left to finish on their own.
    pub fn shutdown(mut self) {
        self.shutdown.store(true, Ordering::SeqCst);
        // Nudge the blocking accept() so it observes the flag.
        match &self.bound {
            Bound::Tcp(addr) => {
                let _ = TcpStream::connect(addr);
            }
            #[cfg(unix)]
            Bound::Unix(path) => {
                let _ = UnixStream::connect(path);
            }
            #[cfg(not(unix))]
            Bound::Unix(_) => {}
        }
        if let Some(handle) = self.accept_thread.take() {
            let _ = handle.join();
        }
        if let Bound::Unix(path) = &self.bound {
            let _ = std::fs::remove_file(path);
        }
    }
}

enum AnyListener {
    Tcp(TcpListener),
    #[cfg(unix)]
    Unix(UnixListener),
}

pub fn start(config: &HttpConfig, host: Arc<ToolHost>) -> anyhow::Result<HttpServer> {
    let (listener, bound) = if let Some(path) = config.bind.strip_prefix("unix:") {
        #[cfg(unix)]
        {
            let path = PathBuf::from(path);
            // A stale socket file from a previous run blocks bind.
            let _ = std::fs::remove_file(&path);
            let listener = UnixListener::bind(&path)
                .with_context(|| format!("failed to bind unix socket `{}`", path.display()))?;
            (AnyListener::Unix(listener), Bound::Unix(path))
        }
        #[cfg(not(unix))]
        {
            let _ = path;
            anyhow::bail!("`unix:` binds are only supported on unix platforms");
        }
    } else {
        let listener = TcpListener::bind(&config.bind)
            .with_context(|| format!("failed to bind `{}`", config.bind))?;
        let addr = listener.local_addr().context("no local addr")?;
        (AnyListener::Tcp(listener), Bound::Tcp(addr))
    };
    let routes: Arc<Vec<RouteEntry>> = Arc::new(
        config
            .routes
            .iter()
            .map(|r| RouteEntry {
                pattern: compile_pattern(&r.path),
                tool: r.tool.clone(),
                content_type: r.content_type.clone(),
                input: r.input,
                output: r.output,
            })
            .collect(),
    );
    let shutdown = Arc::new(AtomicBool::new(false));
    let inflight = Arc::new(AtomicUsize::new(0));
    let max_inflight = config.max_inflight;

    let accept_shutdown = Arc::clone(&shutdown);
    let accept_thread = std::thread::Builder::new()
        .name("sigil-serve-accept".to_owned())
        .spawn(move || match listener {
            AnyListener::Tcp(listener) => {
                for stream in listener.incoming() {
                    if accept_shutdown.load(Ordering::SeqCst) {
                        break;
                    }
                    let Ok(stream) = stream else { continue };
                    let _ = stream.set_read_timeout(Some(IO_TIMEOUT));
                    let _ = stream.set_write_timeout(Some(IO_TIMEOUT));
                    dispatch_connection(stream, &routes, &host, &inflight, max_inflight);
                }
            }
            #[cfg(unix)]
            AnyListener::Unix(listener) => {
                for stream in listener.incoming() {
                    if accept_shutdown.load(Ordering::SeqCst) {
                        break;
                    }
                    let Ok(stream) = stream else { continue };
                    let _ = stream.set_read_timeout(Some(IO_TIMEOUT));
                    let _ = stream.set_write_timeout(Some(IO_TIMEOUT));
                    dispatch_connection(stream, &routes, &host, &inflight, max_inflight);
                }
            }
        })
        .context("failed to spawn accept thread")?;

    Ok(HttpServer {
        bound,
        shutdown,
        accept_thread: Some(accept_thread),
    })
}

/// Shared post-accept path: in-flight capping and the worker spawn.
/// The stream's timeouts are already set by the accept loop.
fn dispatch_connection<S>(
    mut stream: S,
    routes: &Arc<Vec<RouteEntry>>,
    host: &Arc<ToolHost>,
    inflight: &Arc<AtomicUsize>,
    max_inflight: usize,
) where
    S: Read + Write + Send + 'static,
{
    if inflight.load(Ordering::SeqCst) >= max_inflight {
        respond_oneliner(&mut stream, 503, "Service Unavailable", "server busy\n");
        return;
    }
    inflight.fetch_add(1, Ordering::SeqCst);
    let routes = Arc::clone(routes);
    let host = Arc::clone(host);
    let conn_inflight = Arc::clone(inflight);
    let spawned = std::thread::Builder::new()
        .name("sigil-serve-conn".to_owned())
        .spawn(move || {
            handle_connection(&mut stream, &routes, &host);
            conn_inflight.fetch_sub(1, Ordering::SeqCst);
        });
    if spawned.is_err() {
        inflight.fetch_sub(1, Ordering::SeqCst);
    }
}

fn handle_connection<S: Read + Write>(stream: &mut S, routes: &[RouteEntry], host: &ToolHost) {
    // Bytes read past one request's body are the NEXT request's head.
    let mut leftover: Vec<u8> = Vec::new();
    for served in 0..MAX_REQUESTS_PER_CONNECTION {
        let request = match read_request(stream, &mut leftover) {
            Ok(request) => request,
            Err(failure) => {
                // A clean EOF or idle timeout BETWEEN requests is the
                // client hanging up — close without a protocol error.
                if !failure.quiet {
                    respond_oneliner(stream, failure.status, failure.reason, failure.body);
                }
                return;
            }
        };
        let keep_alive = request.keep_alive && served + 1 < MAX_REQUESTS_PER_CONNECTION;

        let Some((route, params)) = match_route(routes, &request.path) else {
            write_response(
                stream,
                404,
                "Not Found",
                "text/plain",
                b"no route for this path\n",
                keep_alive,
            );
            if keep_alive {
                continue;
            }
            return;
        };

        let framed;
        let input: &[u8] = match route.input {
            // Raw: body wins; bodyless requests hand the tool their query
            // string.
            InputMode::Raw => {
                if request.body.is_empty() {
                    request.query.as_bytes()
                } else {
                    &request.body
                }
            }
            InputMode::Envelope => {
                framed = frame_envelope(&request, &params);
                &framed
            }
        };

        match host.execute(&route.tool, input) {
            ToolOutcome::Success(output) => match route.output {
                OutputMode::Raw => {
                    write_response(stream, 200, "OK", &route.content_type, &output, keep_alive);
                }
                OutputMode::Envelope => match decode_response_envelope(&output) {
                    Ok(response) => {
                        write_enveloped_response(stream, route, &response, keep_alive);
                    }
                    Err(problem) => {
                        let body = format!("malformed response envelope: {problem}\n");
                        write_response(
                            stream,
                            500,
                            "Internal Server Error",
                            "text/plain",
                            body.as_bytes(),
                            keep_alive,
                        );
                    }
                },
            },
            ToolOutcome::ToolError(code) => {
                let (status, reason) = map_tool_code(code);
                let body = format!("tool error {code}\n");
                write_response(
                    stream,
                    status,
                    reason,
                    "text/plain",
                    body.as_bytes(),
                    keep_alive,
                );
            }
            ToolOutcome::HostError(message) => {
                let body = format!("{message}\n");
                write_response(
                    stream,
                    500,
                    "Internal Server Error",
                    "text/plain",
                    body.as_bytes(),
                    keep_alive,
                );
            }
        }
        if !keep_alive {
            return;
        }
    }
}

/// The stdlib error-code conventions are HTTP-shaped on purpose: any
/// tool code in [-599, -400] passes through as that HTTP status, which
/// is what lets a dispatching tool answer 405/401/409/… itself.
/// Anything outside the range gets no invented semantics: 500.
fn map_tool_code(code: i64) -> (u16, &'static str) {
    let reason = match code {
        -400 => "Bad Request",
        -401 => "Unauthorized",
        -403 => "Forbidden",
        -404 => "Not Found",
        -405 => "Method Not Allowed",
        -409 => "Conflict",
        -410 => "Gone",
        -413 => "Payload Too Large",
        -422 => "Unprocessable Entity",
        -429 => "Too Many Requests",
        -500 => "Internal Server Error",
        -501 => "Not Implemented",
        -503 => "Service Unavailable",
        (-599..=-400) => "Error",
        _ => return (500, "Internal Server Error"),
    };
    (u16::try_from(-code).expect("range checked"), reason)
}

/// A tool-authored response, decoded from the framed response
/// envelope.
struct EnvelopedResponse {
    status: u16,
    headers: Vec<(String, String)>,
    body: Vec<u8>,
}

/// Response headers the HOST owns. A tool naming any of these is a
/// bug (and `content-length`/`transfer-encoding` would be smuggling
/// vectors if honored) — loud 500, matching the boot-error
/// philosophy elsewhere.
const HOST_OWNED_HEADERS: &[&str] = &["content-length", "connection", "transfer-encoding"];

/// Decode `8-digit ASCII len` + envelope JSON + raw body from tool
/// output; validate everything a tool could use to break the
/// response protocol.
fn decode_response_envelope(output: &[u8]) -> Result<EnvelopedResponse, String> {
    if output.len() < 8 {
        return Err("output shorter than the 8-digit frame".to_owned());
    }
    let mut env_len: usize = 0;
    for &digit in &output[..8] {
        if !digit.is_ascii_digit() {
            return Err("frame is not 8 ASCII digits".to_owned());
        }
        env_len = env_len * 10 + usize::from(digit - b'0');
    }
    let Some(envelope_bytes) = output.get(8..8 + env_len) else {
        return Err(format!(
            "frame declares {env_len} envelope bytes but only {} remain",
            output.len() - 8
        ));
    };
    let envelope: serde_json::Value = serde_json::from_slice(envelope_bytes)
        .map_err(|e| format!("envelope is not valid JSON: {e}"))?;
    let serde_json::Value::Object(fields) = envelope else {
        return Err("envelope must be a JSON object".to_owned());
    };
    for key in fields.keys() {
        if key != "status" && key != "headers" {
            return Err(format!("unknown envelope field `{key}`"));
        }
    }

    let status = match fields.get("status") {
        None => 200,
        Some(value) => {
            let n = value
                .as_u64()
                .ok_or_else(|| "`status` must be a number".to_owned())?;
            if !(100..=599).contains(&n) {
                return Err(format!("`status` {n} outside 100..=599"));
            }
            n as u16
        }
    };

    let mut headers: Vec<(String, String)> = Vec::new();
    if let Some(value) = fields.get("headers") {
        let pairs = value
            .as_array()
            .ok_or_else(|| "`headers` must be an array of [name, value] pairs".to_owned())?;
        for pair in pairs {
            let pair = pair
                .as_array()
                .filter(|p| p.len() == 2)
                .ok_or_else(|| "each header must be a [name, value] pair".to_owned())?;
            let name = pair[0]
                .as_str()
                .ok_or_else(|| "header name must be a string".to_owned())?;
            let value = pair[1]
                .as_str()
                .ok_or_else(|| "header value must be a string".to_owned())?;
            validate_header(name, value)?;
            headers.push((name.to_owned(), value.to_owned()));
        }
    }

    let body = output[8 + env_len..].to_vec();
    if (status == 204 || status == 304) && !body.is_empty() {
        return Err(format!("status {status} must not carry a body"));
    }
    Ok(EnvelopedResponse {
        status,
        headers,
        body,
    })
}

fn validate_header(name: &str, value: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err("empty header name".to_owned());
    }
    if !name
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
    {
        return Err(format!("header name `{name}` has illegal characters"));
    }
    if HOST_OWNED_HEADERS
        .iter()
        .any(|owned| name.eq_ignore_ascii_case(owned))
    {
        return Err(format!("header `{name}` is host-owned"));
    }
    // Response-splitting defense: no CR/LF/NUL, no control bytes
    // beyond tab.
    if value.bytes().any(|b| (b < 0x20 && b != 0x09) || b == 0x7F) {
        return Err(format!("header `{name}` value has control bytes"));
    }
    Ok(())
}

fn write_enveloped_response<S: Write>(
    stream: &mut S,
    route: &RouteEntry,
    response: &EnvelopedResponse,
    keep_alive: bool,
) {
    let has_content_type = response
        .headers
        .iter()
        .any(|(name, _)| name.eq_ignore_ascii_case("content-type"));

    let mut head = format!(
        "HTTP/1.1 {} {}\r\n",
        response.status,
        reason_phrase(response.status)
    );
    for (name, value) in &response.headers {
        head.push_str(&format!("{name}: {value}\r\n"));
    }
    if !has_content_type {
        head.push_str(&format!("Content-Type: {}\r\n", route.content_type));
    }
    let connection = if keep_alive { "keep-alive" } else { "close" };
    head.push_str(&format!(
        "Content-Length: {}\r\nConnection: {connection}\r\n\r\n",
        response.body.len()
    ));
    let _ = stream.write_all(head.as_bytes());
    let _ = stream.write_all(&response.body);
    let _ = stream.flush();
}

/// Reason phrases for the statuses tools plausibly emit; the empty
/// phrase is valid HTTP/1.1 for the rest.
fn reason_phrase(status: u16) -> &'static str {
    match status {
        200 => "OK",
        201 => "Created",
        202 => "Accepted",
        204 => "No Content",
        301 => "Moved Permanently",
        302 => "Found",
        303 => "See Other",
        304 => "Not Modified",
        307 => "Temporary Redirect",
        308 => "Permanent Redirect",
        400 => "Bad Request",
        401 => "Unauthorized",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        409 => "Conflict",
        410 => "Gone",
        413 => "Payload Too Large",
        422 => "Unprocessable Entity",
        429 => "Too Many Requests",
        500 => "Internal Server Error",
        501 => "Not Implemented",
        503 => "Service Unavailable",
        _ => "",
    }
}

/// Build the envelope-mode tool input: an 8-digit ASCII length, the
/// request-envelope JSON, then the raw body bytes. The frame keeps
/// bodies binary-clean — they are never re-encoded into the JSON.
fn frame_envelope(request: &Request, params: &[(String, String)]) -> Vec<u8> {
    let envelope = serde_json::json!({
        "method": request.method,
        "params": params,
        "path": request.path,
        "query": request.query,
        "headers": request.headers,
    });
    let envelope_bytes = envelope.to_string().into_bytes();
    let mut framed = format!("{:08}", envelope_bytes.len()).into_bytes();
    framed.extend_from_slice(&envelope_bytes);
    framed.extend_from_slice(&request.body);
    framed
}

struct Request {
    method: String,
    path: String,
    query: String,
    /// All request headers in arrival order: lowercased name, trimmed
    /// value. (The header block is decoded lossily — URLs and header
    /// values are expected to be ASCII-clean.)
    headers: Vec<(String, String)>,
    body: Vec<u8>,
    /// HTTP/1.1 defaults to persistent; `Connection: close` or
    /// HTTP/1.0 opt out.
    keep_alive: bool,
}

struct RequestFailure {
    status: u16,
    reason: &'static str,
    body: &'static str,
    /// A clean hang-up between requests — close without responding.
    quiet: bool,
}

impl RequestFailure {
    fn new(status: u16, reason: &'static str, body: &'static str) -> Self {
        Self {
            status,
            reason,
            body,
            quiet: false,
        }
    }

    fn quiet_close() -> Self {
        Self {
            status: 0,
            reason: "",
            body: "",
            quiet: true,
        }
    }
}

fn read_request<S: Read + Write>(
    stream: &mut S,
    leftover: &mut Vec<u8>,
) -> Result<Request, RequestFailure> {
    // Start from any bytes the previous request over-read, then
    // accumulate until the blank line, capped.
    let mut buf: Vec<u8> = std::mem::take(leftover);
    let header_end = loop {
        if let Some(pos) = find_subslice(&buf, b"\r\n\r\n") {
            break pos;
        }
        if buf.len() > MAX_HEADER_BYTES {
            return Err(RequestFailure::new(
                431,
                "Request Header Fields Too Large",
                "headers exceed 8 KB\n",
            ));
        }
        let mut chunk = [0u8; 1024];
        let n = match stream.read(&mut chunk) {
            Ok(n) => n,
            Err(_) if buf.is_empty() => return Err(RequestFailure::quiet_close()),
            Err(_) => {
                return Err(RequestFailure::new(
                    408,
                    "Request Timeout",
                    "read timed out\n",
                ));
            }
        };
        if n == 0 {
            if buf.is_empty() {
                // Clean EOF between requests.
                return Err(RequestFailure::quiet_close());
            }
            return Err(RequestFailure::new(
                400,
                "Bad Request",
                "truncated request\n",
            ));
        }
        buf.extend_from_slice(&chunk[..n]);
    };

    let header_text = String::from_utf8_lossy(&buf[..header_end]).into_owned();
    let mut lines = header_text.split("\r\n");
    let request_line = lines.next().unwrap_or("");
    let mut parts = request_line.split(' ');
    let method = parts
        .next()
        .filter(|m| !m.is_empty())
        .ok_or_else(|| RequestFailure::new(400, "Bad Request", "malformed request line\n"))?
        .to_owned();
    let target = parts
        .next()
        .ok_or_else(|| RequestFailure::new(400, "Bad Request", "malformed request line\n"))?;
    let version = parts
        .next()
        .ok_or_else(|| RequestFailure::new(400, "Bad Request", "malformed request line\n"))?;
    if !version.starts_with("HTTP/1.") {
        return Err(RequestFailure::new(
            505,
            "HTTP Version Not Supported",
            "HTTP/1.x only\n",
        ));
    }
    let http_10 = version == "HTTP/1.0";

    let (path, query) = match target.split_once('?') {
        Some((p, q)) => (p.to_owned(), q.to_owned()),
        None => (target.to_owned(), String::new()),
    };

    let mut content_length: usize = 0;
    let mut expects_continue = false;
    let mut connection_close = false;
    let mut headers: Vec<(String, String)> = Vec::new();
    for line in lines {
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        let name = name.trim().to_ascii_lowercase();
        let value = value.trim();
        if name == "content-length" {
            content_length = value
                .parse()
                .map_err(|_| RequestFailure::new(400, "Bad Request", "bad content-length\n"))?;
        } else if name == "expect" && value.eq_ignore_ascii_case("100-continue") {
            expects_continue = true;
        } else if name == "connection" && value.eq_ignore_ascii_case("close") {
            connection_close = true;
        }
        headers.push((name, value.to_owned()));
    }
    if content_length > MAX_BODY_BYTES {
        return Err(RequestFailure::new(
            413,
            "Payload Too Large",
            "body exceeds 5 MB\n",
        ));
    }
    if expects_continue {
        let _ = stream.write_all(b"HTTP/1.1 100 Continue\r\n\r\n");
    }

    // Bytes already read past the header are the body's head; bytes
    // past the body belong to the NEXT request on this connection.
    let mut body = buf[header_end + 4..].to_vec();
    if body.len() > content_length {
        *leftover = body.split_off(content_length);
    }
    while body.len() < content_length {
        let mut chunk = vec![0u8; (content_length - body.len()).min(64 * 1024)];
        let n = stream
            .read(&mut chunk)
            .map_err(|_| RequestFailure::new(408, "Request Timeout", "body read timed out\n"))?;
        if n == 0 {
            return Err(RequestFailure::new(400, "Bad Request", "truncated body\n"));
        }
        body.extend_from_slice(&chunk[..n]);
    }

    Ok(Request {
        method,
        path,
        query,
        headers,
        body,
        keep_alive: !http_10 && !connection_close,
    })
}

fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack
        .windows(needle.len())
        .position(|window| window == needle)
}

fn write_response<S: Write>(
    stream: &mut S,
    status: u16,
    reason: &str,
    content_type: &str,
    body: &[u8],
    keep_alive: bool,
) {
    let connection = if keep_alive { "keep-alive" } else { "close" };
    let head = format!(
        "HTTP/1.1 {status} {reason}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: {connection}\r\n\r\n",
        body.len()
    );
    let _ = stream.write_all(head.as_bytes());
    let _ = stream.write_all(body);
    let _ = stream.flush();
}

fn respond_oneliner<S: Write>(
    stream: &mut S,
    status: u16,
    reason: &'static str,
    body: &'static str,
) {
    write_response(stream, status, reason, "text/plain", body.as_bytes(), false);
}
