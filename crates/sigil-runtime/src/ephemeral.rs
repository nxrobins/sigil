//! Ephemeral (ToolForge) runtime for single-module tool execution.
//!
//! Provides a sandboxed, one-shot execution environment with fuel metering
//! and no actor/message/capability infrastructure.

use std::{
    fmt,
    io::Read,
    sync::{Mutex, OnceLock},
    time::Duration,
};

use wasmtime::{
    Caller, Config, Engine, Error as WasmtimeError, Linker, Module, Result as WasmtimeResult,
    Store, StoreLimits, StoreLimitsBuilder, Val,
};

use crate::alloc_size::AllocBytes;
use crate::grants::{HttpMethod, IoGrants};

/// Maximum file size that can be read via `fs_read` (5 MB).
const MAX_FS_READ_BYTES: usize = 5 * 1024 * 1024;
/// Maximum HTTP response body size (5 MB).
const MAX_HTTP_BODY_BYTES: usize = 5 * 1024 * 1024;
/// Maximum HTTP POST request body copied from guest memory (5 MB).
const MAX_HTTP_REQUEST_BODY_BYTES: usize = 5 * 1024 * 1024;
/// Maximum bytes a tool may return to the host (5 MB).
const MAX_TOOL_OUTPUT_BYTES: usize = 5 * 1024 * 1024;
/// Maximum bytes copied from guest memory for generic FFI byte buffers.
const MAX_FFI_BUFFER_BYTES: usize = 5 * 1024 * 1024;
/// Maximum bytes copied from guest memory for URL/path strings.
const MAX_FFI_STRING_BYTES: usize = 64 * 1024;
/// Maximum linear memory a forge guest can instantiate or grow to (16 MB).
const MAX_GUEST_MEMORY_BYTES: usize = 16 * 1024 * 1024;
/// Hard ceiling for a caller-supplied per-call memory budget (1 GiB). SELF-4:
/// `execute_ephemeral_with_memory_budget` exists so the BOOT-SELF composed
/// compiler (whose ~1 MB self-source needs well past 16 MB across lex/parse/
/// check/emit on a grow-only bump heap) can run WITHOUT widening the default
/// sandbox — but the budget itself must not become an unbounded wall-remover.
/// A request above this ceiling is rejected loudly, never clamped.
const MAX_MEMORY_BUDGET_BYTES: usize = 1024 * 1024 * 1024;
/// Wasmtime fuel backstop for a single tool execution. This is SEPARATE from
/// the cooperative SIGIL `fuel_budget` (which the compiler instruments the
/// guest to charge via a host import): a hand-written or hostile module that
/// never calls that import would otherwise loop forever, since the engine had
/// no fuel/epoch limit at all (finding P1/P2). Wasmtime charges ~1 fuel per
/// executed operation, so this bounds total executed instructions. Sized far
/// above any legitimate tool's instruction count.
const MAX_WASM_FUEL: u64 = 10_000_000_000;
/// Per-socket connect/read/write timeout for blocking HTTP shims.
const HTTP_IO_TIMEOUT: Duration = Duration::from_secs(2);
/// Whole-request timeout for blocking HTTP shims.
const HTTP_TOTAL_TIMEOUT: Duration = Duration::from_secs(2);
/// Maximum number of 3xx redirects followed for a single HTTP shim call.
/// Redirects are NOT followed by the agent (it is built with `.max_redirects(0)`);
/// they are followed manually so every hop is re-validated against the grants.
const MAX_HTTP_REDIRECTS: u32 = 5;
/// Outbound request-header blob cap for `http_post_hdrs` — mirrors
/// sigil-serve's inbound `MAX_HEADER_BYTES` bound.
const MAX_OUTBOUND_HEADER_BYTES: usize = 8 * 1024;
/// Substitute `{{secret:NAME}}` placeholders in an outbound header blob
/// with granted secret values, HOST-SIDE. The result is a fresh String
/// the caller sends but never writes back to guest memory — so the
/// secret bytes never enter the guest. Single pass (a secret value is
/// not re-scanned for placeholders). Errors mirror the shim's HTTP-style
/// codes: 403 for an ungranted secret name, 400 for an unterminated
/// `{{secret:` (no closing `}}`), 500 for a non-UTF-8 secret value (can't
/// go in a header).
fn substitute_secrets(blob: &str, grants: &IoGrants) -> Result<String, u32> {
    const OPEN: &str = "{{secret:";
    const CLOSE: &str = "}}";
    let mut out = String::with_capacity(blob.len());
    let mut rest = blob;
    while let Some(start) = rest.find(OPEN) {
        out.push_str(&rest[..start]);
        let after = &rest[start + OPEN.len()..];
        let Some(end) = after.find(CLOSE) else {
            return Err(400);
        };
        let name = &after[..end];
        let Some(value) = grants.secret_value(name) else {
            return Err(403);
        };
        match std::str::from_utf8(value) {
            Ok(s) => out.push_str(s),
            Err(_) => return Err(500),
        }
        rest = &after[end + CLOSE.len()..];
    }
    out.push_str(rest);
    Ok(out)
}
/// Maximum kv key size (1 KB). Keys are hashed to backing-file names,
/// so the cap bounds shim work, not the storage layout.
const MAX_KV_KEY_BYTES: usize = 1024;
/// Maximum kv value size (5 MB), matching the fs/http body caps.
const MAX_KV_VALUE_BYTES: usize = 5 * 1024 * 1024;
/// Maximum kv namespace label size. Namespaces are exact-match labels
/// against grants — never path components.
const MAX_KV_NAMESPACE_BYTES: usize = 256;
const WASM_PAGE_SIZE: usize = 64 * 1024;

/// Result of a successful tool execution.
#[derive(Debug, Clone)]
pub struct ToolResult {
    pub output: Vec<u8>,
    pub fuel_consumed: u64,
}

/// Errors that can occur during ephemeral tool execution.
#[derive(Debug, Clone)]
pub enum ToolError {
    FuelExhausted { consumed: u64 },
    Trapped { message: String },
    NoEntryPoint,
}

impl fmt::Display for ToolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FuelExhausted { consumed } => {
                write!(f, "tool exhausted fuel budget after {consumed} units")
            }
            Self::Trapped { message } => write!(f, "tool trapped: {message}"),
            Self::NoEntryPoint => write!(f, "no tool_main entry point found"),
        }
    }
}

impl std::error::Error for ToolError {}

/// Pack an error code into the i64 return format (negative, error in low bits).
fn pack_error(code: u32) -> i64 {
    // Use the sign bit to indicate error: -(code as i64)
    -(i64::from(code))
}

/// Pack a pointer and length into the i64 return format.
fn pack_ptr_len(ptr: u32, len: u32) -> i64 {
    ((ptr as i64) << 32) | (len as i64)
}

#[derive(Debug)]
struct GuestMemoryError {
    code: u32,
}

impl GuestMemoryError {
    fn malformed() -> Self {
        Self { code: 400 }
    }

    fn too_large() -> Self {
        Self { code: 413 }
    }
}

fn checked_guest_range(
    memory: &wasmtime::Memory,
    store: &impl wasmtime::AsContext,
    ptr: i32,
    len: i32,
    max_len: usize,
    _label: &str,
) -> Result<(usize, usize), GuestMemoryError> {
    if len < 0 || ptr < 0 {
        return Err(GuestMemoryError::malformed());
    }
    let len = len as usize;
    if len > max_len {
        return Err(GuestMemoryError::too_large());
    }
    let ptr = ptr as usize;
    let end = ptr
        .checked_add(len)
        .ok_or_else(GuestMemoryError::malformed)?;
    if end > memory.data_size(store) {
        return Err(GuestMemoryError::malformed());
    }
    Ok((ptr, len))
}

/// Read a UTF-8 string from guest memory at the given pointer and length.
fn read_guest_string_limited(
    memory: &wasmtime::Memory,
    store: &impl wasmtime::AsContext,
    ptr: i32,
    len: i32,
    max_len: usize,
    label: &str,
) -> Result<String, GuestMemoryError> {
    let (ptr, len) = checked_guest_range(memory, store, ptr, len, max_len, label)?;
    let mut buf = vec![0u8; len];
    memory
        .read(store, ptr, &mut buf)
        .map_err(|_| GuestMemoryError::malformed())?;
    String::from_utf8(buf).map_err(|_| GuestMemoryError::malformed())
}

fn read_guest_bytes_limited(
    memory: &wasmtime::Memory,
    store: &impl wasmtime::AsContext,
    ptr: i32,
    len: i32,
    max_len: usize,
    label: &str,
) -> Result<Vec<u8>, GuestMemoryError> {
    let (ptr, len) = checked_guest_range(memory, store, ptr, len, max_len, label)?;
    let mut buf = vec![0u8; len];
    memory
        .read(store, ptr, &mut buf)
        .map_err(|_| GuestMemoryError::malformed())?;
    Ok(buf)
}

fn ensure_guest_capacity(
    memory: &wasmtime::Memory,
    store: &mut impl wasmtime::AsContextMut<Data = EphemeralData>,
    required_end: u64,
) -> Result<(), String> {
    let current_size = memory.data_size(&mut *store) as u64;
    if required_end <= current_size {
        return Ok(());
    }
    // SELF-4: the per-call budget (default MAX_GUEST_MEMORY_BYTES) rides the
    // store data so this shim-side check and the wasmtime StoreLimits wall
    // always agree for the SAME execution.
    let budget = store.as_context().data().memory_budget as u64;
    if required_end > budget {
        return Err("guest allocation exceeds forge memory limit".into());
    }

    let additional_bytes = required_end - current_size;
    let additional_pages = additional_bytes.div_ceil(WASM_PAGE_SIZE as u64);
    memory
        .grow(&mut *store, additional_pages)
        .map_err(|e| e.to_string())?;
    Ok(())
}

fn alloc_from_bump(
    memory: &wasmtime::Memory,
    bump_global: &wasmtime::Global,
    store: &mut impl wasmtime::AsContextMut<Data = EphemeralData>,
    size: AllocBytes,
) -> Result<u32, String> {
    let ptr = bump_global.get(&mut *store).unwrap_i32() as u32;
    let new_ptr = ptr
        .checked_add(size.get())
        .ok_or_else(|| "guest allocation overflowed BUMP_PTR".to_owned())?;
    ensure_guest_capacity(memory, &mut *store, u64::from(new_ptr))?;
    bump_global
        .set(&mut *store, Val::I32(new_ptr as i32))
        .map_err(|e| e.to_string())?;
    Ok(ptr)
}

fn get_guest_memory_and_bump(
    caller: &mut Caller<'_, EphemeralData>,
) -> Result<(wasmtime::Memory, wasmtime::Global), String> {
    let memory = match caller.get_export("memory") {
        Some(wasmtime::Extern::Memory(memory)) => memory,
        _ => return Err("no memory export".into()),
    };
    let bump_global = match caller.get_export("BUMP_PTR") {
        Some(wasmtime::Extern::Global(global)) => global,
        _ => return Err("no BUMP_PTR export".into()),
    };
    Ok((memory, bump_global))
}

/// Backing file for a kv key under `root`: file name is the SHA-256
/// hex of the key bytes. Key bytes therefore never participate in path
/// resolution — no traversal surface, and any byte sequence up to the
/// cap is a valid key.
fn kv_key_path(root: &std::path::Path, key: &[u8]) -> std::path::PathBuf {
    use sha2::Digest;
    let digest = sha2::Sha256::digest(key);
    let mut name: String = digest.iter().map(|b| format!("{b:02x}")).collect();
    name.push_str(".kv");
    root.join(name)
}

fn parse_http_url(url: &str, grants: &IoGrants, method: HttpMethod) -> Result<String, u32> {
    let parsed = url::Url::parse(url).map_err(|_| 400u32)?;
    match parsed.scheme() {
        "http" | "https" => {}
        _ => return Err(400u32),
    }

    let host = parsed.host_str().ok_or(400u32)?.to_ascii_lowercase();
    if !grants.net_allowed(&host, method) {
        return Err(403u32);
    }

    Ok(parsed.to_string())
}

fn read_http_body(response: ureq::http::Response<ureq::Body>) -> Result<Vec<u8>, u32> {
    let mut reader = response
        .into_body()
        .into_reader()
        .take((MAX_HTTP_BODY_BYTES + 1) as u64);
    let mut body = Vec::new();
    reader.read_to_end(&mut body).map_err(|_| 502u32)?;
    if body.len() > MAX_HTTP_BODY_BYTES {
        return Err(413u32);
    }
    Ok(body)
}

/// Hard wall-clock bound for ONE PHASE of an HTTP shim call — a single hop
/// (connect + request + response headers) or the body read — enforced host-side.
/// ureq's own `timeout_global` is the first line of defense but is RACY against
/// a slow-dribbling peer whose chunk cadence collides with the deadline
/// (observed on ureq 3.3.0: the same 2s-deadline request against a 100ms-dribble
/// server sometimes aborts at 2.0s and sometimes runs to completion — an
/// exactly-expired deadline becomes a 1s grace read, `NextTimeout::not_zero`) —
/// the guest-facing anti-hang bound must not depend on it. 500ms of grace past
/// `HTTP_TOTAL_TIMEOUT` lets the library timeout fire first when it does work.
///
/// The bound is PER PHASE, not per call: ureq constructs a fresh global timer
/// for every `agent` call, and `http_fetch`'s manual redirect loop issues up to
/// `1 + MAX_HTTP_REDIRECTS` of them, so the design's own legitimate budget for
/// a redirect chain is that many timers plus the body read. A whole-call bound
/// of one window would 502 redirect chains that each hop legitimately clears.
const HTTP_WATCHDOG_TIMEOUT: Duration =
    HTTP_TOTAL_TIMEOUT.saturating_add(Duration::from_millis(500));

/// Process-wide cap on concurrently outstanding HTTP shim worker threads. A
/// watchdog expiry detaches its worker, and ureq's per-read grace window never
/// gives up against a peer that keeps dribbling (see `HTTP_WATCHDOG_TIMEOUT`),
/// so each expiry can pin one thread + socket for as long as the granted peer
/// dribbles. `execute_ephemeral` runs IN-PROCESS inside the long-lived
/// sigil-mcp server, where those leaks would accumulate across tool runs
/// without bound; at the cap, new shim calls fail closed with 502 instead of
/// spawning. Sized far above any legitimate tool's concurrent-call count.
const MAX_OUTSTANDING_HTTP_WORKERS: usize = 64;

static OUTSTANDING_HTTP_WORKERS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// Watchdog heartbeat protocol between the shim worker and the guest-facing
/// receiver: `Hop` opens a fresh `HTTP_WATCHDOG_TIMEOUT` window (sent after
/// each completed redirect hop and once before the body read); `Done` carries
/// the final result.
enum HttpProgress {
    Hop,
    Done(Result<Vec<u8>, u32>),
}

/// Issue `http_fetch` and read the response body on a detached worker thread,
/// bounding EACH PHASE (every redirect hop, then the body read) by
/// `HTTP_WATCHDOG_TIMEOUT` wall-clock via the `HttpProgress` heartbeat, and the
/// number of windows by the same hop budget `http_fetch` itself enforces. A
/// watchdog expiry maps to 502 exactly like a library-level transport failure.
///
/// The worker is detached: its late result lands in a dropped channel. Against
/// an adversarial forever-dribbling peer the thread lives as long as the peer
/// dribbles (ureq's expired-deadline grace read never gives up) — that is
/// strictly better than stalling the guest, and the leak is bounded by
/// `MAX_OUTSTANDING_HTTP_WORKERS` across the process, which matters for the
/// long-lived sigil-mcp server. Worst-case guest-visible latency is one window
/// per budgeted phase (`2 + MAX_HTTP_REDIRECTS` windows).
fn http_fetch_body_bounded(
    method: HttpMethod,
    url: String,
    body: Option<Vec<u8>>,
    grants: &IoGrants,
    // Caller-supplied outbound request headers (`http_post_hdrs` /
    // `http_post_secret`); empty for the plain GET/POST shims. Owned so the
    // worker thread can take them.
    headers: Vec<(String, String)>,
) -> Result<Vec<u8>, u32> {
    use std::sync::atomic::Ordering;

    let grants = grants.clone();
    let (tx, rx) = std::sync::mpsc::channel();

    // Reserve a worker slot; fail closed at the cap (leaked dribble-pinned
    // workers keep holding their slots until their peers give up).
    let prev = OUTSTANDING_HTTP_WORKERS.fetch_add(1, Ordering::SeqCst);
    if prev >= MAX_OUTSTANDING_HTTP_WORKERS {
        OUTSTANDING_HTTP_WORKERS.fetch_sub(1, Ordering::SeqCst);
        return Err(502u32);
    }

    let worker_tx = tx.clone();
    let spawned = std::thread::Builder::new()
        .name("sigil-http-shim".to_owned())
        .spawn(move || {
            // Release the slot when the worker exits, however it exits.
            struct SlotGuard;
            impl Drop for SlotGuard {
                fn drop(&mut self) {
                    OUTSTANDING_HTTP_WORKERS.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
                }
            }
            let _slot = SlotGuard;
            let result = http_fetch(method, url, body.as_deref(), &grants, &headers, &worker_tx)
                .and_then(|response| {
                    // Fresh window for the body read: headers arrived, the
                    // hop's window no longer applies.
                    let _ = worker_tx.send(HttpProgress::Hop);
                    read_http_body(response)
                });
            let _ = worker_tx.send(HttpProgress::Done(result));
        });
    if spawned.is_err() {
        // Thread exhaustion must degrade to a tool error, not unwind through
        // the wasmtime host closure and take the host process down.
        OUTSTANDING_HTTP_WORKERS.fetch_sub(1, Ordering::SeqCst);
        return Err(502u32);
    }
    drop(tx);

    // One window for the initial hop, one per followable redirect, one for the
    // body read. `http_fetch` bounds its own loop to the same hop budget, so a
    // conforming worker can never exhaust these windows without producing
    // `Done`; if it somehow does, fail closed.
    for _ in 0..(2 + MAX_HTTP_REDIRECTS as usize) {
        match rx.recv_timeout(HTTP_WATCHDOG_TIMEOUT) {
            Ok(HttpProgress::Done(result)) => return result,
            Ok(HttpProgress::Hop) => continue,
            // Timeout, or the worker died without sending (its channel end
            // dropped — e.g. a panic inside ureq): fail closed either way.
            Err(_) => return Err(502u32),
        }
    }
    Err(502u32)
}

fn http_agent() -> ureq::Agent {
    use ureq::tls::{RootCerts, TlsConfig};
    ureq::Agent::config_builder()
        // Whole-request + connect timeouts so a slow/hung peer cannot stall the
        // sandboxed tool indefinitely.
        .timeout_global(Some(HTTP_TOTAL_TIMEOUT))
        .timeout_connect(Some(HTTP_IO_TIMEOUT))
        // Do NOT let ureq auto-follow redirects: it would fetch the redirect
        // target WITHOUT re-checking it against the grants, so an allowed host
        // could 3xx-redirect to an ungranted or internal host and bypass the
        // network grant (finding P1). With max_redirects(0) a 3xx is returned to
        // us as an ordinary response; `http_fetch` follows manually, re-
        // validating scheme/host/method on every hop.
        .max_redirects(0)
        // Return 4xx/5xx as responses rather than errors, so `http_fetch`
        // branches uniformly on `status()` (transport failures still surface as
        // `Err`). Preserves the old behavior of returning the HTTP status code
        // to the guest.
        .http_status_as_error(false)
        // Trust the platform (OS) certificate store — the public web AND any
        // private/enterprise CAs installed on the host. rustls-platform-verifier
        // uses rustls-native-certs 0.8 / rustls-pki-types (NOT the unmaintained
        // rustls-pemfile, RUSTSEC-2025-0134).
        .tls_config(
            TlsConfig::builder()
                .root_certs(RootCerts::PlatformVerifier)
                .build(),
        )
        // Honor HTTP(S)_PROXY / NO_PROXY from the environment (parity with the
        // old `proxy-from-env` feature). The grant check runs on the request URL
        // before any request, so a proxy cannot widen the reachable host set.
        .proxy(ureq::Proxy::try_from_env())
        .build()
        .new_agent()
}

/// Resolve a redirect `Location` against the URL that produced it and
/// re-validate the target the same way the initial URL was validated:
/// scheme must be http/https and the host must be granted for `method`.
/// Handles absolute and relative `Location` values via URL joining. Returns
/// the validated absolute target, or a guest error code (`403` for a
/// disallowed scheme/host, `502` for an unparseable Location/base).
fn validate_redirect_target(
    current: &str,
    location: &str,
    grants: &IoGrants,
    method: HttpMethod,
) -> Result<String, u32> {
    let base = url::Url::parse(current).map_err(|_| 502u32)?;
    let target = base.join(location).map_err(|_| 502u32)?;
    match target.scheme() {
        "http" | "https" => {}
        _ => return Err(403u32),
    }
    let host = target.host_str().ok_or(403u32)?.to_ascii_lowercase();
    if !grants.net_allowed(&host, method) {
        return Err(403u32);
    }
    Ok(target.to_string())
}

/// Method to use for the request that follows a 3xx redirect, given the
/// response status and the current method. Mirrors standard client behaviour:
/// 301/302/303 downgrade a POST to a bodyless GET (the "POST/redirect/GET"
/// idiom — 303 mandates it, 301/302 do it by near-universal convention);
/// 307/308 preserve the method and body. GET stays GET in all cases.
fn redirect_method(status: u16, current: HttpMethod) -> HttpMethod {
    match status {
        301..=303 => HttpMethod::Get,
        _ => current,
    }
}

/// Issue an HTTP request and follow up to `MAX_HTTP_REDIRECTS` redirects,
/// re-validating scheme/host/method against the grants on every hop and
/// bounding the hop count. The agent has auto-redirects disabled, so a 3xx is
/// returned to us as a normal response; we read its `Location`, re-check it,
/// and re-issue. Closes the grant bypass where an allowed host redirects to an
/// ungranted/internal host (finding P1). `initial_url` must already have been
/// validated by `parse_http_url`.
///
/// `watchdog` is the shim watchdog heartbeat (see `http_fetch_body_bounded`):
/// each followed redirect sends `HttpProgress::Hop` to open a fresh window,
/// mirroring the fresh ureq global timer the next `agent` call gets. Send
/// failures are ignored — the receiver drops its end after a watchdog expiry,
/// and the worker's remaining work is then invisible by design.
fn http_fetch(
    method: HttpMethod,
    initial_url: String,
    body: Option<&[u8]>,
    grants: &IoGrants,
    headers: &[(String, String)],
    watchdog: &std::sync::mpsc::Sender<HttpProgress>,
) -> Result<ureq::http::Response<ureq::Body>, u32> {
    let agent = http_agent();
    let mut url = initial_url;
    let mut method = method;
    // Own the body so it can be dropped on a POST→GET downgrade.
    let mut body: Vec<u8> = body.map(<[u8]>::to_vec).unwrap_or_default();
    // initial request + up to MAX_HTTP_REDIRECTS follow-ups.
    for _ in 0..=MAX_HTTP_REDIRECTS {
        let outcome = match method {
            HttpMethod::Get => {
                let mut req = agent.get(&url);
                for (name, value) in headers {
                    req = req.header(name, value);
                }
                req.call()
            }
            HttpMethod::Post => {
                let mut req = agent.post(&url);
                for (name, value) in headers {
                    req = req.header(name, value);
                }
                req.send(body.as_slice())
            }
        };
        // The agent is configured with `http_status_as_error(false)` and
        // `max_redirects(0)`, so 3xx/4xx/5xx all come back as `Ok(response)` and
        // the only `Err` is a transport-level failure (connect/timeout/TLS).
        let response = outcome.map_err(|_| 502u32)?;
        let status = response.status().as_u16();
        if (300..400).contains(&status) {
            // Copy the target out so the immutable borrow of `response` ends
            // before we mutate `url`/`method` and drop the response.
            let location = response
                .headers()
                .get(ureq::http::header::LOCATION)
                .and_then(|v| v.to_str().ok())
                .ok_or(502u32)?
                .to_owned();
            // SECRET-BEARING REDIRECT: with caller-supplied headers (which may
            // carry a host-injected secret) a 3xx leaves only unsafe options —
            // forward the header to the redirect target (a different, possibly
            // merely-also-granted host now sees the secret) or drop it silently
            // (the retry loses its auth and the failure is inscrutable). Refuse
            // instead. The header-less shims keep following redirects exactly as
            // before, so this narrows nothing that worked.
            if !headers.is_empty() {
                return Err(403u32);
            }
            let next_method = redirect_method(status, method);
            // Re-validate the redirect target against the grants — using the
            // method we will ACTUALLY use on the next hop — before touching it.
            url = validate_redirect_target(&url, &location, grants, next_method)?;
            // A POST downgraded to GET carries no body forward.
            if matches!(method, HttpMethod::Post) && matches!(next_method, HttpMethod::Get) {
                body = Vec::new();
            }
            method = next_method;
            // Following a redirect: the next hop gets a fresh ureq global
            // timer, so open a fresh watchdog window to match.
            let _ = watchdog.send(HttpProgress::Hop);
            continue;
        }
        if status >= 400 {
            // Surface the HTTP status code to the guest, as the 2.x path did.
            return Err(u32::from(status));
        }
        return Ok(response);
    }
    // Exceeded the hop budget.
    Err(310u32)
}

#[cfg(test)]
mod http_redirect_tests {
    use super::{redirect_method, validate_redirect_target};
    use crate::grants::{HttpMethod, IoGrants, NetGrant};

    #[test]
    fn post_downgrades_to_get_on_301_302_303() {
        for status in [301u16, 302, 303] {
            assert_eq!(
                redirect_method(status, HttpMethod::Post),
                HttpMethod::Get,
                "status {status} must downgrade POST to GET"
            );
        }
    }

    #[test]
    fn post_is_preserved_on_307_308() {
        assert_eq!(redirect_method(307, HttpMethod::Post), HttpMethod::Post);
        assert_eq!(redirect_method(308, HttpMethod::Post), HttpMethod::Post);
    }

    #[test]
    fn get_stays_get_across_all_redirect_codes() {
        for status in [301u16, 302, 303, 307, 308] {
            assert_eq!(redirect_method(status, HttpMethod::Get), HttpMethod::Get);
        }
    }

    fn grants_for(host: &str, method: HttpMethod) -> IoGrants {
        IoGrants {
            net: vec![NetGrant {
                host_pattern: host.into(),
                methods: vec![method],
            }],
            ..Default::default()
        }
    }

    #[test]
    fn redirect_to_ungranted_host_is_rejected() {
        // The classic SSRF pivot: an allowed host 302s to the cloud metadata
        // service. Only the original host was granted, so this must be refused.
        let grants = grants_for("127.0.0.1", HttpMethod::Get);
        assert_eq!(
            validate_redirect_target(
                "http://127.0.0.1:8080/start",
                "http://169.254.169.254/latest/meta-data/",
                &grants,
                HttpMethod::Get,
            ),
            Err(403)
        );
    }

    #[test]
    fn redirect_to_granted_host_is_allowed() {
        let grants = grants_for("127.0.0.1", HttpMethod::Get);
        assert_eq!(
            validate_redirect_target(
                "http://127.0.0.1:8080/start",
                "http://127.0.0.1:8080/next",
                &grants,
                HttpMethod::Get,
            ),
            Ok("http://127.0.0.1:8080/next".to_string())
        );
    }

    #[test]
    fn relative_redirect_stays_on_same_host() {
        let grants = grants_for("127.0.0.1", HttpMethod::Get);
        assert_eq!(
            validate_redirect_target("http://127.0.0.1:8080/a/b", "/c", &grants, HttpMethod::Get),
            Ok("http://127.0.0.1:8080/c".to_string())
        );
    }

    #[test]
    fn redirect_to_non_http_scheme_is_rejected() {
        let grants = grants_for("127.0.0.1", HttpMethod::Get);
        assert_eq!(
            validate_redirect_target(
                "http://127.0.0.1:8080/start",
                "file:///etc/passwd",
                &grants,
                HttpMethod::Get,
            ),
            Err(403)
        );
    }

    #[test]
    fn redirect_method_is_re_checked_against_the_grant() {
        // Host granted for GET only; a POST that redirects to the same host
        // must be refused because POST is not granted there.
        let grants = grants_for("127.0.0.1", HttpMethod::Get);
        assert_eq!(
            validate_redirect_target(
                "http://127.0.0.1:8080/start",
                "http://127.0.0.1:8080/next",
                &grants,
                HttpMethod::Post,
            ),
            Err(403)
        );
    }
}

/// Write `body` to `path`, refusing to follow a symlink at the final path
/// component. The FsWrite grant is checked against the canonicalized parent
/// plus the file name, but a plain `std::fs::write` would still follow a
/// symlink placed at that final name — e.g. a grant for `/allowed` plus
/// `/allowed/link -> /etc/passwd` writes outside the grant (finding P1).
///
/// On Unix this opens with `O_NOFOLLOW`, which fails atomically (`ELOOP`)
/// when the final component is a symlink — closing both the grant escape
/// and the check-then-write TOCTOU window in one syscall. The parent is
/// already canonicalized by the caller, so parent-directory symlinks are
/// resolved before the grant check. Returns the guest-facing error code:
/// `403` for a symlink/escape attempt, `500` for any other I/O failure.
fn write_no_follow(path: &std::path::Path, body: &[u8]) -> Result<(), u32> {
    #[cfg(unix)]
    {
        use std::io::Write as _;
        use std::os::unix::fs::OpenOptionsExt as _;
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(path)
            .map_err(|e| match e.raw_os_error() {
                // ELOOP: the final component is a symlink — a grant-escape
                // attempt. (Some platforms report ELOOP as EMLINK-adjacent;
                // O_NOFOLLOW is specified to yield ELOOP.)
                Some(code) if code == libc::ELOOP => 403u32,
                _ => 500u32,
            })?;
        file.write_all(body).map_err(|_| 500u32)?;
        Ok(())
    }
    #[cfg(not(unix))]
    {
        // Portable fallback for platforms without O_NOFOLLOW: reject if the
        // final component is a symlink. `symlink_metadata` does not follow
        // it. Not fully atomic — a narrow TOCTOU remains — but it closes the
        // persistent-symlink escape.
        if let Ok(meta) = std::fs::symlink_metadata(path)
            && meta.file_type().is_symlink()
        {
            return Err(403);
        }
        std::fs::write(path, body).map_err(|_| 500u32)
    }
}

#[cfg(all(test, unix))]
mod fs_write_no_follow_tests {
    use super::write_no_follow;
    use std::path::PathBuf;

    fn unique_dir(tag: &str) -> PathBuf {
        use std::time::{SystemTime, UNIX_EPOCH};
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let mut p = std::env::temp_dir();
        p.push(format!(
            "sigil_nofollow_{}_{}_{}",
            tag,
            std::process::id(),
            nanos
        ));
        std::fs::create_dir_all(&p).expect("temp dir");
        p
    }

    #[test]
    fn rejects_final_component_symlink_and_does_not_write_through() {
        // /allowed/link -> /outside/secret. A grant for /allowed passes the
        // caller's fs_write_allowed check on the link path, so the ONLY thing
        // standing between the guest and /outside/secret is the no-follow open.
        let allowed = unique_dir("allowed");
        let outside = unique_dir("outside");
        let secret = outside.join("secret.txt");
        std::fs::write(&secret, b"original").expect("seed secret");
        let link = allowed.join("link.txt");
        std::os::unix::fs::symlink(&secret, &link).expect("make symlink");

        let result = write_no_follow(&link, b"pwned");

        assert_eq!(result, Err(403), "write through a symlink must be refused");
        assert_eq!(
            std::fs::read(&secret).expect("read secret"),
            b"original",
            "the out-of-grant target must be untouched"
        );

        let _ = std::fs::remove_dir_all(&allowed);
        let _ = std::fs::remove_dir_all(&outside);
    }

    #[test]
    fn creates_a_new_regular_file() {
        let dir = unique_dir("newfile");
        let target = dir.join("out.txt");
        assert!(write_no_follow(&target, b"hello").is_ok());
        assert_eq!(std::fs::read(&target).expect("read"), b"hello");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn overwrites_an_existing_regular_file() {
        let dir = unique_dir("overwrite");
        let target = dir.join("out.txt");
        std::fs::write(&target, b"old-and-longer").expect("seed");
        assert!(write_no_follow(&target, b"new").is_ok());
        assert_eq!(
            std::fs::read(&target).expect("read"),
            b"new",
            "truncate must apply on overwrite"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}

/// Write bytes to guest memory at the current BUMP_PTR and advance the pointer.
/// Returns the guest pointer where data was written.
fn write_to_guest(
    memory: &wasmtime::Memory,
    bump_global: &wasmtime::Global,
    store: &mut impl wasmtime::AsContextMut<Data = EphemeralData>,
    data: &[u8],
) -> Result<u32, String> {
    let ptr = alloc_from_bump(
        memory,
        bump_global,
        &mut *store,
        AllocBytes::from_host_len(data.len() as u32),
    )?;
    memory
        .write(&mut *store, ptr as usize, data)
        .map_err(|e| e.to_string())?;
    Ok(ptr)
}

/// Store data for the ephemeral runtime — tracks fuel consumption and,
/// when a `RandomGrant::Seeded` is present, the per-execution PRNG
/// state. Per-execution lifetime is enforced by the wasmtime `Store`
/// being dropped at the end of `execute_ephemeral`: state cannot leak
/// across calls.
struct EphemeralData {
    fuel_remaining: u64,
    /// Set by the `fuel_decrement` shim when a decrement is refused because the
    /// declared budget is exhausted. The shim then raises a wasmtime trap, so the
    /// guest cannot observe or continue past the refusal. Read by
    /// `execute_ephemeral_inner` to distinguish a fuel trap from every other trap
    /// PRECISELY — `fuel_remaining == 0` alone is ambiguous, since a tool may legally
    /// consume its budget to the last unit and then trap for an unrelated reason.
    fuel_exhausted: bool,
    /// Seeded xorshift64* state. `Some(seed)` at execute_ephemeral
    /// entry when grants contain `RandomGrant::Seeded`; `None`
    /// otherwise. Mutated by the `random_bytes` shim.
    random_state: Option<u64>,
    /// SELF-4: the per-call linear-memory budget in bytes. Defaults to
    /// MAX_GUEST_MEMORY_BYTES; `execute_ephemeral_with_memory_budget` raises
    /// it for a single execution (≤ MAX_MEMORY_BUDGET_BYTES). Read by the
    /// host-side alloc shim (`ensure_guest_capacity`) so the shim check and
    /// the wasmtime StoreLimits wall below always agree.
    memory_budget: usize,
    limits: StoreLimits,
}

fn store_data(fuel_budget: u64, grants: &IoGrants, memory_budget: usize) -> EphemeralData {
    EphemeralData {
        fuel_remaining: fuel_budget,
        fuel_exhausted: false,
        random_state: grants.seeded_random(),
        memory_budget,
        limits: StoreLimitsBuilder::new()
            .memory_size(memory_budget)
            .memories(1)
            .instances(1)
            .trap_on_grow_failure(true)
            .build(),
    }
}

/// Compile `wasm_bytes` to a wasmtime `(Engine, Module)`, reusing the most
/// recently compiled pair when the bytes are byte-identical.
///
/// Cranelift-compiling a multi-MB module costs ~seconds. The self-hosted
/// differential test suites call `execute_ephemeral` with the SAME merged tool
/// 100+ times (varying only the input), so without this the identical module is
/// recompiled on every call — the dominant CI cost (`typecheck_differential` was
/// ~369s, ~33% of the rust job). Caching the immutable compiled `Module` collapses
/// that to a single compile; each `execute_ephemeral` call still builds a FRESH
/// `Store`/`Instance`/`Linker`, so execution stays fully ephemeral (no state
/// leaks across calls — only the read-only compiled code is shared).
///
/// Bounded to a SINGLE entry (replaced when the bytes differ) so a long-lived
/// host that runs many distinct tools cannot grow this cache without bound.
fn engine_and_module(wasm_bytes: &[u8]) -> Result<(Engine, Module), ToolError> {
    /// The single cached entry: the exact wasm bytes plus the compiled pair.
    type CachedModule = (Vec<u8>, Engine, Module);
    static CACHE: OnceLock<Mutex<Option<CachedModule>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(None));
    let mut slot = cache
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some((bytes, engine, module)) = slot.as_ref()
        && bytes.as_slice() == wasm_bytes
    {
        return Ok((engine.clone(), module.clone()));
    }
    // Preserve Module::new's legacy support for WAT as well as binary Wasm.
    // Inspect the exact normalized binary that will be compiled, so text is
    // neither accidentally rejected nor a way to hide host requirements.
    // A cache hit above is safe: only checked modules are inserted below, and
    // the key is the entire original input, including all custom sections.
    let binary = wat::parse_bytes(wasm_bytes).map_err(|error| ToolError::Trapped {
        message: error.to_string(),
    })?;
    // A module compiled against the ephemeral host's own declared profile runs here; one that
    // requires any other profile, or none at all in the legacy shape, is handled exactly as
    // before (accepted as legacy, or refused as bound to a host this is not).
    crate::host_contract::check_host_profile_requirement(
        &binary,
        &crate::ephemeral_profile::ephemeral_host_profile(),
    )
    .map_err(|error| ToolError::Trapped {
        message: error.to_string(),
    })?;
    // Enable fuel consumption on the engine so a per-execution wasmtime fuel
    // budget can be enforced (see `execute_ephemeral`). Without this, arbitrary
    // wasm could spin forever without ever calling the cooperative SIGIL fuel
    // host import (finding P1/P2).
    let mut config = Config::new();
    config.consume_fuel(true);
    let engine = Engine::new(&config).map_err(|e| ToolError::Trapped {
        message: e.to_string(),
    })?;
    let module = Module::from_binary(&engine, &binary).map_err(|e| ToolError::Trapped {
        message: e.to_string(),
    })?;
    *slot = Some((wasm_bytes.to_vec(), engine.clone(), module.clone()));
    Ok((engine, module))
}

/// Execute a compiled tool module in an ephemeral sandbox.
///
/// The tool receives `input` bytes via guest memory (written at the BUMP_PTR
/// location) and is expected to return a packed i64 where the upper 32 bits
/// are the result pointer and the lower 32 bits are the result length. A
/// return value of -1 indicates an error.
pub fn execute_ephemeral(
    wasm_bytes: &[u8],
    input: &[u8],
    fuel_budget: u64,
    grants: &IoGrants,
) -> Result<ToolResult, ToolError> {
    execute_ephemeral_inner(
        wasm_bytes,
        input,
        fuel_budget,
        MAX_WASM_FUEL,
        MAX_GUEST_MEMORY_BYTES,
        grants,
    )
}

/// SELF-4: [`execute_ephemeral`] with a raised PER-CALL linear-memory budget.
/// The default 16 MB sandbox (`MAX_GUEST_MEMORY_BYTES`) is unchanged for every
/// other caller — this exists for the BOOT-SELF composed self-hosted compiler,
/// whose ~1 MB self-source outgrows 16 MB across lex/parse/check/emit on the
/// grow-only bump heap. A budget above [`MAX_MEMORY_BUDGET_BYTES`] (1 GiB) is
/// rejected loudly, never clamped.
pub fn execute_ephemeral_with_memory_budget(
    wasm_bytes: &[u8],
    input: &[u8],
    fuel_budget: u64,
    memory_budget: usize,
    grants: &IoGrants,
) -> Result<ToolResult, ToolError> {
    if memory_budget > MAX_MEMORY_BUDGET_BYTES {
        return Err(ToolError::Trapped {
            message: format!(
                "memory budget {memory_budget} exceeds the {MAX_MEMORY_BUDGET_BYTES}-byte ceiling"
            ),
        });
    }
    execute_ephemeral_inner(
        wasm_bytes,
        input,
        fuel_budget,
        MAX_WASM_FUEL,
        memory_budget,
        grants,
    )
}

/// Test seam: [`execute_ephemeral`] with an explicit wasmtime fuel cap (tests
/// inject a small cap to exercise the backstop without running billions of ops).
#[cfg(test)]
fn execute_ephemeral_with_wasm_fuel(
    wasm_bytes: &[u8],
    input: &[u8],
    fuel_budget: u64,
    wasm_fuel_cap: u64,
    grants: &IoGrants,
) -> Result<ToolResult, ToolError> {
    execute_ephemeral_inner(
        wasm_bytes,
        input,
        fuel_budget,
        wasm_fuel_cap,
        MAX_GUEST_MEMORY_BYTES,
        grants,
    )
}

/// Backing implementation: explicit wasmtime fuel cap AND per-call memory budget.
fn execute_ephemeral_inner(
    wasm_bytes: &[u8],
    input: &[u8],
    fuel_budget: u64,
    wasm_fuel_cap: u64,
    memory_budget: usize,
    grants: &IoGrants,
) -> Result<ToolResult, ToolError> {
    // The compiled `(Engine, Module)` is cached and reused across calls with the
    // same bytes (see `engine_and_module`); only the read-only compiled code is
    // shared — the Store/Instance/Linker below are fresh per call.
    let (engine, module) = engine_and_module(wasm_bytes)?;
    let mut linker = Linker::new(&engine);

    link_sigil_imports(&mut linker)?;
    link_ffi_imports(&mut linker, grants)?;

    // Validate grants up front (cap counts + Seeded(0) rejection).
    grants.validate().map_err(|e| ToolError::Trapped {
        message: e.to_string(),
    })?;

    let mut store = Store::new(&engine, store_data(fuel_budget, grants, memory_budget));
    store.limiter(|data| &mut data.limits);
    // Wasmtime fuel backstop: bound total executed instructions so a module
    // that never calls the cooperative SIGIL fuel import cannot loop forever.
    // The engine has `consume_fuel(true)`, so the store starts with 0 fuel and
    // MUST be given a budget here or it would trap immediately.
    store
        .set_fuel(wasm_fuel_cap)
        .map_err(|e| ToolError::Trapped {
            message: e.to_string(),
        })?;

    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| ToolError::Trapped {
            message: e.to_string(),
        })?;

    // Write input to guest memory via BUMP_PTR.
    let memory = instance
        .get_memory(&mut store, "memory")
        .ok_or(ToolError::Trapped {
            message: "no memory export".into(),
        })?;
    let bump_global = instance
        .get_global(&mut store, "BUMP_PTR")
        .ok_or(ToolError::Trapped {
            message: "no BUMP_PTR export".into(),
        })?;
    if input.len() > memory_budget {
        return Err(ToolError::Trapped {
            message: "tool input length exceeds forge memory limit".into(),
        });
    }
    let input_len = u32::try_from(input.len()).map_err(|_| ToolError::Trapped {
        message: "tool input length exceeds forge memory limit".into(),
    })?;
    let base_ptr = alloc_from_bump(
        &memory,
        &bump_global,
        &mut store,
        AllocBytes::from_host_len(input_len),
    )
    .map_err(|e| ToolError::Trapped { message: e })? as usize;
    memory
        .write(&mut store, base_ptr, input)
        .map_err(|e| ToolError::Trapped {
            message: e.to_string(),
        })?;

    // Find tool_main — try exact "tool__tool_main" first, then search exports.
    let tool_func = find_tool_main(&instance, &mut store).ok_or(ToolError::NoEntryPoint)?;

    // Call tool_main(input_ptr, input_len) -> i64.
    // The function signature depends on how the tool is compiled — Sigil
    // uses i64 for all integer types at the Wasm level.
    let ty = tool_func.ty(&store);
    let params: Vec<Val> = ty
        .params()
        .enumerate()
        .map(|(i, param_ty)| {
            let val = if i == 0 {
                base_ptr as i64
            } else {
                input.len() as i64
            };
            match param_ty {
                wasmtime::ValType::I32 => Val::I32(val as i32),
                wasmtime::ValType::I64 => Val::I64(val),
                _ => Val::I64(val),
            }
        })
        .collect();
    let result_count = ty.results().len();
    let mut results = vec![Val::I64(0); result_count];
    match tool_func.call(&mut store, &params, &mut results) {
        Ok(()) => {}
        Err(e) => {
            // Classify on the shim's explicit flag, not on `fuel_remaining == 0`:
            // a tool may legally consume its budget to the last unit and then trap
            // for an unrelated reason, which the old inference misreported as fuel.
            if store.data().fuel_exhausted {
                return Err(ToolError::FuelExhausted {
                    consumed: fuel_budget,
                });
            }
            return Err(ToolError::Trapped {
                message: format!("{e:#}"),
            });
        }
    }

    // Read the result.
    let fuel_consumed = fuel_budget - store.data().fuel_remaining;
    let packed = if results.is_empty() {
        0i64
    } else {
        match &results[0] {
            Val::I64(v) => *v,
            Val::I32(v) => i64::from(*v),
            _ => 0i64,
        }
    };
    if packed < 0 {
        return Err(ToolError::Trapped {
            message: format!("tool returned error ({})", -packed),
        });
    }
    let result_ptr = ((packed >> 32) as u32) as usize;
    let result_len = ((packed & 0xFFFF_FFFF) as u32) as usize;
    if result_len == 0 {
        return Ok(ToolResult {
            output: vec![],
            fuel_consumed,
        });
    }
    if result_len > MAX_TOOL_OUTPUT_BYTES {
        return Err(ToolError::Trapped {
            message: "tool output length exceeds forge limit".into(),
        });
    }
    let result_end = result_ptr
        .checked_add(result_len)
        .ok_or(ToolError::Trapped {
            message: "tool output range overflowed guest memory".into(),
        })?;
    if result_end > memory.data_size(&store) {
        return Err(ToolError::Trapped {
            message: "tool output range exceeds guest memory".into(),
        });
    }
    let mut output = vec![0u8; result_len];
    memory
        .read(&store, result_ptr, &mut output)
        .map_err(|e| ToolError::Trapped {
            message: e.to_string(),
        })?;

    Ok(ToolResult {
        output,
        fuel_consumed,
    })
}

/// Register the standard Sigil host imports.
/// Actor and capability operations trap because forge tools cannot use them.
fn link_sigil_imports(linker: &mut Linker<EphemeralData>) -> Result<(), ToolError> {
    let wrap_err = |e: wasmtime::Error| ToolError::Trapped {
        message: e.to_string(),
    };

    // fuel_decrement(amount: i32)
    //
    // ENFORCED (not advisory): a decrement that would overrun the declared budget is
    // REFUSED and raises a wasmtime trap, unwinding the guest immediately. This mirrors
    // the actor runtime, whose `fuel_decrement_import` returns
    // `RuntimeError::FuelExhausted` (runtime.rs:586-588) — before this, the two paths
    // disagreed and only the actor one honoured the declared budget.
    //
    // The wasm-visible import type is UNCHANGED: a host fn returning `Result<(), Error>`
    // still has wasm type `(i32) -> ()` (errors become traps, not a return value), so the
    // compiler's emitted bytes (wasm.rs:281, wasm.rs:1357-1360) need no change and the
    // BOOT-SELF byte capstone stays green.
    linker
        .func_wrap(
            "sigil",
            "fuel_decrement",
            |mut caller: Caller<'_, EphemeralData>, amount: i32| -> WasmtimeResult<()> {
                let data = caller.data_mut();
                let cost = u64::try_from(amount)
                    .map_err(|_| WasmtimeError::msg("fuel decrement must be non-negative"))?;
                if cost > data.fuel_remaining {
                    // Refuse the decrement, do NOT saturate. Saturating both let the
                    // tool run past its budget AND made the overrun arithmetically
                    // invisible (`consumed == budget` exactly).
                    data.fuel_exhausted = true;
                    return Err(WasmtimeError::msg("fuel exhausted"));
                }
                data.fuel_remaining -= cost;
                Ok(())
            },
        )
        .map_err(wrap_err)?;

    // fuel_exhausted()
    linker
        .func_wrap(
            "sigil",
            "fuel_exhausted",
            |_caller: Caller<'_, EphemeralData>| {},
        )
        .map_err(wrap_err)?;

    // alloc(size: i32) -> i32 — reserve space from the guest's BUMP_PTR heap.
    linker
        .func_wrap(
            "sigil",
            "alloc",
            |mut caller: Caller<'_, EphemeralData>, size: i32| -> WasmtimeResult<i32> {
                // The guest-size contract is enforced by the type: the only way to reach
                // `alloc_from_bump` is with an `AllocBytes`, and the only way to make one is
                // a named constructor (alloc_size.rs). For a guest `i32`, that constructor
                // performs the sign check. The actor host routes through the same type.
                let size = AllocBytes::checked_from_guest(size)
                    .map_err(|e| WasmtimeError::msg(e.to_string()))?;
                let (memory, bump_global) =
                    get_guest_memory_and_bump(&mut caller).map_err(WasmtimeError::msg)?;
                let ptr = alloc_from_bump(&memory, &bump_global, &mut caller, size)
                    .map_err(WasmtimeError::msg)?;
                Ok(ptr as i32)
            },
        )
        .map_err(wrap_err)?;

    // Actor + capability ops trap in tool mode. These belong to the actor execution model; the
    // forge implements none of them. They used to be SILENT no-ops returning 0 — the one
    // outcome the security model cannot afford, because it is the only failure mode with no
    // signal on any channel. A guest that reaches one (only hostile hand-written wasm can —
    // a legal tool cannot obtain the ActorRef/Fuel/&Admin to call them, and the compiler will
    // M011 gate rejects actor machinery in a tool) now traps loudly instead.
    // Each is a `func_wrap` returning `Err`, so the wasm import TYPE is unchanged and no
    // emitted byte moves.
    fn not_in_forge(op: &str) -> WasmtimeError {
        WasmtimeError::msg(format!(
            "`{op}` is not available in the forge execution model (it belongs to the actor \
             model); a tool must not call it"
        ))
    }
    linker
        .func_wrap(
            "sigil",
            "send",
            |_: Caller<'_, EphemeralData>, _: i32, _: i32, _: i32, _: i32| -> WasmtimeResult<()> {
                Err(not_in_forge("send"))
            },
        )
        .map_err(wrap_err)?;
    linker
        .func_wrap(
            "sigil",
            "ask",
            |_: Caller<'_, EphemeralData>,
             _: i32,
             _: i32,
             _: i32,
             _: i32,
             _: i64|
             -> WasmtimeResult<i64> { Err(not_in_forge("ask")) },
        )
        .map_err(wrap_err)?;
    linker
        .func_wrap(
            "sigil",
            "spawn",
            |_: Caller<'_, EphemeralData>,
             _: i32,
             _: i32,
             _: i32,
             _: i32,
             _: i32|
             -> WasmtimeResult<i32> { Err(not_in_forge("spawn")) },
        )
        .map_err(wrap_err)?;
    linker
        .func_wrap(
            "sigil",
            "cap_restrict",
            |_: Caller<'_, EphemeralData>, _: i32, _: i32| -> WasmtimeResult<i32> {
                Err(not_in_forge("cap_restrict"))
            },
        )
        .map_err(wrap_err)?;
    linker
        .func_wrap(
            "sigil",
            "cap_split",
            |_: Caller<'_, EphemeralData>, _: i32, _: i64| -> WasmtimeResult<i32> {
                Err(not_in_forge("cap_split"))
            },
        )
        .map_err(wrap_err)?;
    linker
        .func_wrap(
            "sigil",
            "cap_mint",
            |_: Caller<'_, EphemeralData>| -> WasmtimeResult<i32> { Err(not_in_forge("cap_mint")) },
        )
        .map_err(wrap_err)?;

    Ok(())
}

/// Register FFI host functions in the "ffi" namespace.
/// Grant checking happens inside each function body at call time.
fn link_ffi_imports(
    linker: &mut Linker<EphemeralData>,
    grants: &IoGrants,
) -> Result<(), ToolError> {
    let wrap_err = |e: wasmtime::Error| ToolError::Trapped {
        message: e.to_string(),
    };

    // http_get(url_ptr, url_len) -> i64 packed (ptr << 32 | len)
    let grants_for_get = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "http_get",
            move |mut caller: Caller<'_, EphemeralData>, url_ptr: i32, url_len: i32| -> i64 {
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let url = match read_guest_string_limited(
                    &memory,
                    &caller,
                    url_ptr,
                    url_len,
                    MAX_FFI_STRING_BYTES,
                    "http url",
                ) {
                    Ok(url) => url,
                    Err(err) => return pack_error(err.code),
                };
                let url = match parse_http_url(&url, &grants_for_get, HttpMethod::Get) {
                    Ok(url) => url,
                    Err(code) => return pack_error(code),
                };
                let body = match http_fetch_body_bounded(
                    HttpMethod::Get,
                    url,
                    None,
                    &grants_for_get,
                    Vec::new(),
                ) {
                    Ok(body) => body,
                    Err(code) => return pack_error(code),
                };
                match write_to_guest(&memory, &bump_global, &mut caller, &body) {
                    Ok(ptr) => pack_ptr_len(ptr, body.len() as u32),
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // http_post(url_ptr, url_len, body_ptr, body_len) -> i64 packed (ptr << 32 | len)
    let grants_for_post = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "http_post",
            move |mut caller: Caller<'_, EphemeralData>,
                  url_ptr: i32,
                  url_len: i32,
                  body_ptr: i32,
                  body_len: i32|
                  -> i64 {
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let url = match read_guest_string_limited(
                    &memory,
                    &caller,
                    url_ptr,
                    url_len,
                    MAX_FFI_STRING_BYTES,
                    "http url",
                ) {
                    Ok(url) => url,
                    Err(err) => return pack_error(err.code),
                };
                let url = match parse_http_url(&url, &grants_for_post, HttpMethod::Post) {
                    Ok(url) => url,
                    Err(code) => return pack_error(code),
                };
                let request_body = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    body_ptr,
                    body_len,
                    MAX_HTTP_REQUEST_BODY_BYTES,
                    "http request body",
                ) {
                    Ok(body) => body,
                    Err(err) => return pack_error(err.code),
                };
                let response_body = match http_fetch_body_bounded(
                    HttpMethod::Post,
                    url,
                    Some(request_body),
                    &grants_for_post,
                    Vec::new(),
                ) {
                    Ok(body) => body,
                    Err(code) => return pack_error(code),
                };
                match write_to_guest(&memory, &bump_global, &mut caller, &response_body) {
                    Ok(ptr) => pack_ptr_len(ptr, response_body.len() as u32),
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // fs_read — real implementation with grant checking
    // http_post_hdrs(url_ptr, url_len, body_ptr, body_len, hdrs_ptr, hdrs_len) -> i64 packed.
    // POST with caller-supplied request headers, so tools can speak to authenticated APIs
    // (e.g. `x-api-key` + `anthropic-version`). Headers arrive as a newline-separated
    // "Name: Value" blob — bounded at 8 KB, mirroring sigil-serve's inbound header cap.
    // A malformed line (no ':') is a caller bug → 400. Same NetGrant check and response
    // body cap as `http_post`.
    let grants_for_post_hdrs = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "http_post_hdrs",
            move |mut caller: Caller<'_, EphemeralData>,
                  url_ptr: i32,
                  url_len: i32,
                  body_ptr: i32,
                  body_len: i32,
                  hdrs_ptr: i32,
                  hdrs_len: i32|
                  -> i64 {
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let url = match read_guest_string_limited(
                    &memory,
                    &caller,
                    url_ptr,
                    url_len,
                    MAX_FFI_STRING_BYTES,
                    "http url",
                ) {
                    Ok(url) => url,
                    Err(err) => return pack_error(err.code),
                };
                let url = match parse_http_url(&url, &grants_for_post_hdrs, HttpMethod::Post) {
                    Ok(url) => url,
                    Err(code) => return pack_error(code),
                };
                let request_body = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    body_ptr,
                    body_len,
                    MAX_HTTP_REQUEST_BODY_BYTES,
                    "http request body",
                ) {
                    Ok(body) => body,
                    Err(err) => return pack_error(err.code),
                };
                if hdrs_len as usize > MAX_OUTBOUND_HEADER_BYTES {
                    return pack_error(431);
                }
                let hdrs_blob = match read_guest_string_limited(
                    &memory,
                    &caller,
                    hdrs_ptr,
                    hdrs_len,
                    MAX_OUTBOUND_HEADER_BYTES,
                    "http request headers",
                ) {
                    Ok(blob) => blob,
                    Err(err) => return pack_error(err.code),
                };
                let mut headers: Vec<(String, String)> = Vec::new();
                for line in hdrs_blob.lines() {
                    let line = line.trim();
                    if line.is_empty() {
                        continue;
                    }
                    let Some((name, value)) = line.split_once(':') else {
                        return pack_error(400);
                    };
                    headers.push((name.trim().to_owned(), value.trim().to_owned()));
                }
                // Main's bounded fetch (watchdog + per-hop grant re-validation)
                // instead of a raw ureq call: the raw path auto-followed
                // redirects, which could hand these headers — including an
                // injected secret — to a host the grant never authorized. A 3xx
                // with headers present now fails closed.
                let response_body = match http_fetch_body_bounded(
                    HttpMethod::Post,
                    url,
                    Some(request_body),
                    &grants_for_post_hdrs,
                    headers,
                ) {
                    Ok(body) => body,
                    Err(code) => return pack_error(code),
                };
                match write_to_guest(&memory, &bump_global, &mut caller, &response_body) {
                    Ok(ptr) => pack_ptr_len(ptr, response_body.len() as u32),
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // http_post_secret(url_ptr, url_len, body_ptr, body_len, hdrs_ptr, hdrs_len) -> i64 packed.
    // Like http_post_hdrs, but the header blob may contain `{{secret:NAME}}`
    // placeholders that the HOST substitutes with granted SecretGrant values
    // BEFORE sending. The substituted blob is built host-side and never written
    // back into guest memory — so the secret (e.g. an api key) never enters the
    // guest at all: there are no secret bytes in guest memory to read, copy, or
    // launder. A placeholder naming an ungranted secret is -403; an unterminated
    // placeholder is -400. Same NetGrant check and response cap as http_post_hdrs.
    let grants_for_post_secret = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "http_post_secret",
            move |mut caller: Caller<'_, EphemeralData>,
                  url_ptr: i32,
                  url_len: i32,
                  body_ptr: i32,
                  body_len: i32,
                  hdrs_ptr: i32,
                  hdrs_len: i32|
                  -> i64 {
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let url = match read_guest_string_limited(
                    &memory,
                    &caller,
                    url_ptr,
                    url_len,
                    MAX_FFI_STRING_BYTES,
                    "http url",
                ) {
                    Ok(url) => url,
                    Err(err) => return pack_error(err.code),
                };
                let url = match parse_http_url(&url, &grants_for_post_secret, HttpMethod::Post) {
                    Ok(url) => url,
                    Err(code) => return pack_error(code),
                };
                let request_body = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    body_ptr,
                    body_len,
                    MAX_HTTP_REQUEST_BODY_BYTES,
                    "http request body",
                ) {
                    Ok(body) => body,
                    Err(err) => return pack_error(err.code),
                };
                if hdrs_len as usize > MAX_OUTBOUND_HEADER_BYTES {
                    return pack_error(431);
                }
                // The blob read from the guest holds only PLACEHOLDERS.
                let placeholder_blob = match read_guest_string_limited(
                    &memory,
                    &caller,
                    hdrs_ptr,
                    hdrs_len,
                    MAX_OUTBOUND_HEADER_BYTES,
                    "http request headers",
                ) {
                    Ok(blob) => blob,
                    Err(err) => return pack_error(err.code),
                };
                // Substitute host-side into a fresh String — never returned to guest.
                let hdrs_blob = match substitute_secrets(&placeholder_blob, &grants_for_post_secret)
                {
                    Ok(blob) => blob,
                    Err(code) => return pack_error(code),
                };
                let mut headers: Vec<(String, String)> = Vec::new();
                for line in hdrs_blob.lines() {
                    let line = line.trim();
                    if line.is_empty() {
                        continue;
                    }
                    let Some((name, value)) = line.split_once(':') else {
                        return pack_error(400);
                    };
                    headers.push((name.trim().to_owned(), value.trim().to_owned()));
                }
                // Main's bounded fetch (watchdog + per-hop grant re-validation)
                // instead of a raw ureq call: the raw path auto-followed
                // redirects, which could hand these headers — including an
                // injected secret — to a host the grant never authorized. A 3xx
                // with headers present now fails closed.
                let response_body = match http_fetch_body_bounded(
                    HttpMethod::Post,
                    url,
                    Some(request_body),
                    &grants_for_post_secret,
                    headers,
                ) {
                    Ok(body) => body,
                    Err(code) => return pack_error(code),
                };
                match write_to_guest(&memory, &bump_global, &mut caller, &response_body) {
                    Ok(ptr) => pack_ptr_len(ptr, response_body.len() as u32),
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // fs_read — real implementation with grant checking
    let grants_for_fs = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "fs_read",
            move |mut caller: Caller<'_, EphemeralData>, path_ptr: i32, path_len: i32| -> i64 {
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let path_str = match read_guest_string_limited(
                    &memory,
                    &caller,
                    path_ptr,
                    path_len,
                    MAX_FFI_STRING_BYTES,
                    "fs path",
                ) {
                    Ok(s) => s,
                    Err(err) => return pack_error(err.code),
                };
                let canonical = match std::fs::canonicalize(&path_str) {
                    Ok(p) => p,
                    Err(_) => return pack_error(404),
                };
                if !grants_for_fs.fs_read_allowed(&canonical) {
                    crate::trace::shim_exit("fs_read", pack_error(403), 0);
                    return pack_error(403);
                }
                let data = match std::fs::read(&canonical) {
                    Ok(d) if d.len() <= MAX_FS_READ_BYTES => d,
                    Ok(_) => return pack_error(413),
                    Err(_) => return pack_error(404),
                };
                match write_to_guest(&memory, &bump_global, &mut caller, &data) {
                    Ok(ptr) => pack_ptr_len(ptr, data.len() as u32),
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // fs_list(path_ptr, path_len) -> i64 packed.
    // Directory listing: the SORTED, newline-joined entry file names of the
    // directory at `path`. Grant-checked with the SAME fs read grant as
    // fs_read (listing is a read). Sorting makes the output deterministic —
    // std::fs::read_dir order is OS-dependent, and non-determinism would
    // break byte-exact grading. -400 malformed path, -404 missing or
    // not-a-directory, -403 ungranted, -413 over the 5 MB cap, -500 host.
    let grants_for_fs_list = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "fs_list",
            move |mut caller: Caller<'_, EphemeralData>, path_ptr: i32, path_len: i32| -> i64 {
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let path_str = match read_guest_string_limited(
                    &memory,
                    &caller,
                    path_ptr,
                    path_len,
                    MAX_FFI_STRING_BYTES,
                    "fs path",
                ) {
                    Ok(s) => s,
                    Err(err) => return pack_error(err.code),
                };
                let canonical = match std::fs::canonicalize(&path_str) {
                    Ok(p) => p,
                    Err(_) => return pack_error(404),
                };
                if !grants_for_fs_list.fs_read_allowed(&canonical) {
                    crate::trace::shim_exit("fs_list", pack_error(403), 0);
                    return pack_error(403);
                }
                let read_dir = match std::fs::read_dir(&canonical) {
                    Ok(rd) => rd,
                    Err(_) => return pack_error(404), // not a directory, or gone
                };
                let mut names: Vec<String> = Vec::new();
                for entry in read_dir {
                    match entry {
                        Ok(e) => names.push(e.file_name().to_string_lossy().into_owned()),
                        Err(_) => return pack_error(500),
                    }
                }
                names.sort();
                let listing = names.join("\n").into_bytes();
                if listing.len() > MAX_FS_READ_BYTES {
                    return pack_error(413);
                }
                match write_to_guest(&memory, &bump_global, &mut caller, &listing) {
                    Ok(ptr) => pack_ptr_len(ptr, listing.len() as u32),
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // ── Phase 5a-2 shims ────────────────────────────────────────────────

    // fs_write(path_ptr, path_len, body_ptr, body_len) -> i64
    // Returns 0 on success, packed error code on failure.
    let grants_for_fs_write = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "fs_write",
            move |mut caller: Caller<'_, EphemeralData>,
                  path_ptr: i32,
                  path_len: i32,
                  body_ptr: i32,
                  body_len: i32|
                  -> i64 {
                use crate::trace;
                // Optimistic entry log; the shim_exit below carries the
                // actual outcome (allow/reject) via result_code.
                trace::shim_entry("fs_write", trace::GrantDecision::Allowed);
                let (memory, _bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let path_str = match read_guest_string_limited(
                    &memory,
                    &caller,
                    path_ptr,
                    path_len,
                    MAX_FFI_STRING_BYTES,
                    "fs path",
                ) {
                    Ok(s) => s,
                    Err(err) => return pack_error(err.code),
                };
                let body = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    body_ptr,
                    body_len,
                    MAX_FS_READ_BYTES,
                    "fs write body",
                ) {
                    Ok(b) => b,
                    Err(err) => return pack_error(err.code),
                };
                if body.len() > MAX_FS_READ_BYTES {
                    return pack_error(413);
                }
                // Path canonicalization for write requires the parent
                // directory to exist (the file may not yet). Resolve the
                // parent and re-attach the file name.
                let path = std::path::Path::new(&path_str);
                let canonical_parent =
                    match path.parent().and_then(|p| std::fs::canonicalize(p).ok()) {
                        Some(p) => p,
                        None => return pack_error(404),
                    };
                let file_name = match path.file_name() {
                    Some(n) => n,
                    None => return pack_error(400),
                };
                let canonical = canonical_parent.join(file_name);
                if !grants_for_fs_write.fs_write_allowed(&canonical) {
                    trace::shim_exit("fs_write", pack_error(403), 0);
                    return pack_error(403);
                }
                // Write with no-follow semantics on the final component: the
                // grant was checked against `canonical`, but a symlink placed
                // at that path would otherwise let `std::fs::write` escape the
                // grant (finding P1). See `write_no_follow`.
                match write_no_follow(&canonical, &body) {
                    Ok(()) => {
                        trace::shim_exit("fs_write", 0, body.len() as u32);
                        0
                    }
                    Err(code) => {
                        trace::shim_exit("fs_write", pack_error(code), 0);
                        pack_error(code)
                    }
                }
            },
        )
        .map_err(wrap_err)?;

    // ── KV storage shims ────────────────────────────────────────────────
    //
    // Durable key-value storage behind namespace grants. The namespace
    // selects a grant (exact string match, fail closed); the grant's
    // `root` directory is where bytes live; keys map to files by
    // SHA-256 hex. Durability = `std::fs::write` + atomic rename,
    // matching `fs_write`'s OS write-back semantics.

    // kv_get(ns_ptr, ns_len, key_ptr, key_len) -> i64
    // Packed value bytes; -403 no read grant, -404 key absent,
    // -400 bad args, -413 key/value over cap, -500 host failure.
    let grants_for_kv_get = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "kv_get",
            move |mut caller: Caller<'_, EphemeralData>,
                  ns_ptr: i32,
                  ns_len: i32,
                  key_ptr: i32,
                  key_len: i32|
                  -> i64 {
                use crate::trace;
                trace::shim_entry("kv_get", trace::GrantDecision::Allowed);
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let namespace = match read_guest_string_limited(
                    &memory,
                    &caller,
                    ns_ptr,
                    ns_len,
                    MAX_KV_NAMESPACE_BYTES,
                    "kv namespace",
                ) {
                    Ok(s) => s,
                    Err(err) => return pack_error(err.code),
                };
                let key = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    key_ptr,
                    key_len,
                    MAX_KV_KEY_BYTES,
                    "kv key",
                ) {
                    Ok(k) => k,
                    Err(err) => return pack_error(err.code),
                };
                let root = match grants_for_kv_get.kv_read_root(&namespace) {
                    Some(r) => r.to_path_buf(),
                    None => {
                        trace::shim_exit("kv_get", pack_error(403), 0);
                        return pack_error(403);
                    }
                };
                let data = match std::fs::read(kv_key_path(&root, &key)) {
                    Ok(d) if d.len() <= MAX_KV_VALUE_BYTES => d,
                    Ok(_) => return pack_error(413),
                    Err(_) => return pack_error(404),
                };
                match write_to_guest(&memory, &bump_global, &mut caller, &data) {
                    Ok(ptr) => {
                        let result = pack_ptr_len(ptr, data.len() as u32);
                        trace::shim_exit("kv_get", result, data.len() as u32);
                        result
                    }
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // kv_put(ns_ptr, ns_len, key_ptr, key_len, val_ptr, val_len) -> i64
    // 0 on success; -403 no write grant, -400 bad args, -413 over cap,
    // -500 host failure (including a missing grant root — creating the
    // root is the granter's job, not the tool's).
    let grants_for_kv_put = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "kv_put",
            move |mut caller: Caller<'_, EphemeralData>,
                  ns_ptr: i32,
                  ns_len: i32,
                  key_ptr: i32,
                  key_len: i32,
                  val_ptr: i32,
                  val_len: i32|
                  -> i64 {
                use crate::trace;
                trace::shim_entry("kv_put", trace::GrantDecision::Allowed);
                let (memory, _bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let namespace = match read_guest_string_limited(
                    &memory,
                    &caller,
                    ns_ptr,
                    ns_len,
                    MAX_KV_NAMESPACE_BYTES,
                    "kv namespace",
                ) {
                    Ok(s) => s,
                    Err(err) => return pack_error(err.code),
                };
                let key = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    key_ptr,
                    key_len,
                    MAX_KV_KEY_BYTES,
                    "kv key",
                ) {
                    Ok(k) => k,
                    Err(err) => return pack_error(err.code),
                };
                let value = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    val_ptr,
                    val_len,
                    MAX_KV_VALUE_BYTES,
                    "kv value",
                ) {
                    Ok(v) => v,
                    Err(err) => return pack_error(err.code),
                };
                let root = match grants_for_kv_put.kv_write_root(&namespace) {
                    Some(r) => r.to_path_buf(),
                    None => {
                        trace::shim_exit("kv_put", pack_error(403), 0);
                        return pack_error(403);
                    }
                };
                let final_path = kv_key_path(&root, &key);
                // Atomic publish: write a sibling temp file, then rename
                // over the final name. A concurrent reader sees either
                // the old value or the new one, never a torn write.
                let tmp_path = final_path.with_extension("kv.tmp");
                if std::fs::write(&tmp_path, &value).is_err() {
                    return pack_error(500);
                }
                match std::fs::rename(&tmp_path, &final_path) {
                    Ok(()) => {
                        trace::shim_exit("kv_put", 0, value.len() as u32);
                        0
                    }
                    Err(_) => {
                        let _ = std::fs::remove_file(&tmp_path);
                        pack_error(500)
                    }
                }
            },
        )
        .map_err(wrap_err)?;

    // kv_delete(ns_ptr, ns_len, key_ptr, key_len) -> i64
    // 0 on success; -404 key absent, -403 no write grant, -400 bad
    // args, -413 key over cap, -500 host failure.
    let grants_for_kv_delete = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "kv_delete",
            move |mut caller: Caller<'_, EphemeralData>,
                  ns_ptr: i32,
                  ns_len: i32,
                  key_ptr: i32,
                  key_len: i32|
                  -> i64 {
                use crate::trace;
                trace::shim_entry("kv_delete", trace::GrantDecision::Allowed);
                let (memory, _bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let namespace = match read_guest_string_limited(
                    &memory,
                    &caller,
                    ns_ptr,
                    ns_len,
                    MAX_KV_NAMESPACE_BYTES,
                    "kv namespace",
                ) {
                    Ok(s) => s,
                    Err(err) => return pack_error(err.code),
                };
                let key = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    key_ptr,
                    key_len,
                    MAX_KV_KEY_BYTES,
                    "kv key",
                ) {
                    Ok(k) => k,
                    Err(err) => return pack_error(err.code),
                };
                let root = match grants_for_kv_delete.kv_write_root(&namespace) {
                    Some(r) => r.to_path_buf(),
                    None => {
                        trace::shim_exit("kv_delete", pack_error(403), 0);
                        return pack_error(403);
                    }
                };
                match std::fs::remove_file(kv_key_path(&root, &key)) {
                    Ok(()) => {
                        trace::shim_exit("kv_delete", 0, 0);
                        0
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => pack_error(404),
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // crypto_sha256(input_ptr, input_len) -> i64 packed pointer to 32 bytes
    linker
        .func_wrap(
            "ffi",
            "crypto_sha256",
            move |mut caller: Caller<'_, EphemeralData>, input_ptr: i32, input_len: i32| -> i64 {
                use crate::trace;
                trace::shim_entry("crypto_sha256", trace::GrantDecision::NotRequired);
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let input = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    input_ptr,
                    input_len,
                    MAX_FFI_BUFFER_BYTES,
                    "sha256 input",
                ) {
                    Ok(b) => b,
                    Err(err) => return pack_error(err.code),
                };
                use sha2::Digest;
                let digest = sha2::Sha256::digest(&input);
                match write_to_guest(&memory, &bump_global, &mut caller, digest.as_slice()) {
                    Ok(ptr) => {
                        let result = pack_ptr_len(ptr, 32);
                        trace::shim_exit("crypto_sha256", result, 32);
                        result
                    }
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // crypto_sha512(input_ptr, input_len) -> i64 packed pointer to 64 bytes
    linker
        .func_wrap(
            "ffi",
            "crypto_sha512",
            move |mut caller: Caller<'_, EphemeralData>, input_ptr: i32, input_len: i32| -> i64 {
                use crate::trace;
                trace::shim_entry("crypto_sha512", trace::GrantDecision::NotRequired);
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                let input = match read_guest_bytes_limited(
                    &memory,
                    &caller,
                    input_ptr,
                    input_len,
                    MAX_FFI_BUFFER_BYTES,
                    "sha512 input",
                ) {
                    Ok(b) => b,
                    Err(err) => return pack_error(err.code),
                };
                use sha2::Digest;
                let digest = sha2::Sha512::digest(&input);
                match write_to_guest(&memory, &bump_global, &mut caller, digest.as_slice()) {
                    Ok(ptr) => {
                        let result = pack_ptr_len(ptr, 64);
                        trace::shim_exit("crypto_sha512", result, 64);
                        result
                    }
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // time_now() -> i64 — Unix epoch milliseconds.
    // Grant precedence: Frozen(ms) > Wall > -403.
    //   - Frozen present → return the frozen ms verbatim (deterministic).
    //   - Wall present → return SystemTime::now() (may decrease, I18).
    //   - Neither → -403 (rejected).
    let grants_for_time = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "time_now",
            move |_: Caller<'_, EphemeralData>| -> i64 {
                use crate::trace;
                let frozen = grants_for_time.frozen_time();
                let wall_allowed = grants_for_time.time_allowed(crate::grants::TimeGrant::Wall);
                let allowed = frozen.is_some() || wall_allowed;
                let decision = if allowed {
                    trace::GrantDecision::Allowed
                } else {
                    trace::GrantDecision::Rejected
                };
                trace::shim_entry("time_now", decision);
                if !allowed {
                    let result = pack_error(403);
                    trace::shim_exit("time_now", result, 0);
                    return result;
                }
                let now = match frozen {
                    Some(ms) => ms,
                    None => std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .map(|d| d.as_millis() as i64)
                        .unwrap_or(0),
                };
                trace::shim_exit("time_now", now, 0);
                now
            },
        )
        .map_err(wrap_err)?;

    // random_bytes(out_len) -> i64 packed pointer.
    // Per I26: out_len capped at 64 KB to prevent fuel-burn DoS.
    //
    // Grant precedence: Seeded > Secure > -403.
    //   - Seeded path: caller.data_mut().random_state is the per-execution
    //     xorshift64* state (Some at this point because execute_ephemeral
    //     primed it from grants.seeded_random()). Each call advances the
    //     state; output is deterministic for a given (seed, call sequence).
    //   - Secure path: getrandom-backed CSPRNG (nondeterministic).
    //   - Neither: -403.
    let grants_for_random = grants.clone();
    linker
        .func_wrap(
            "ffi",
            "random_bytes",
            move |mut caller: Caller<'_, EphemeralData>, out_len: i32| -> i64 {
                use crate::trace;
                let seeded_present = caller.data().random_state.is_some();
                let secure_allowed =
                    grants_for_random.random_allowed(crate::grants::RandomGrant::Secure);
                let allowed = seeded_present || secure_allowed;
                let decision = if allowed {
                    trace::GrantDecision::Allowed
                } else {
                    trace::GrantDecision::Rejected
                };
                trace::shim_entry("random_bytes", decision);
                if !allowed {
                    return pack_error(403);
                }
                // Reject zero-length too: `random_bytes(0)` would return
                // a 0-byte buffer whose contents are unspecified — a
                // SIGIL caller doing `load8(ptr)` reads stale bump-area
                // memory. Fail loudly at the FFI boundary.
                if out_len <= 0 || out_len > MAX_RANDOM_BYTES as i32 {
                    return pack_error(400);
                }
                let mut buf = vec![0u8; out_len as usize];
                if seeded_present {
                    let state = caller
                        .data_mut()
                        .random_state
                        .as_mut()
                        .expect("seeded_present implies Some");
                    fill_seeded(state, &mut buf);
                } else if getrandom::getrandom(&mut buf).is_err() {
                    return pack_error(500);
                }
                let (memory, bump_global) = match get_guest_memory_and_bump(&mut caller) {
                    Ok(exports) => exports,
                    Err(_) => return pack_error(500),
                };
                match write_to_guest(&memory, &bump_global, &mut caller, &buf) {
                    Ok(ptr) => {
                        let result = pack_ptr_len(ptr, buf.len() as u32);
                        trace::shim_exit("random_bytes", result, buf.len() as u32);
                        result
                    }
                    Err(_) => pack_error(500),
                }
            },
        )
        .map_err(wrap_err)?;

    // ── Self-hosting Cap<Z3> shim (feature-gated; NC5/CM5) ───────────────
    // z3_check(query_ptr, query_len) -> i64. SMT-LIB2 query in guest memory;
    // returns sat(1) / unsat(0), or a NEGATIVE code. A non-{sat,unsat}
    // outcome is NEVER reported as 0/1 (NC1). Authority is checked FIRST,
    // before any read/parse/solver work (NC2). Compiled only under
    // `--features solver`, so a default runtime build links no Z3 and
    // registers no `z3_check` import (the import is simply unprovided).
    #[cfg(feature = "solver")]
    {
        let grants_for_z3 = grants.clone();
        linker
            .func_wrap(
                "ffi",
                "z3_check",
                move |mut caller: Caller<'_, EphemeralData>,
                      query_ptr: i32,
                      query_len: i32|
                      -> i64 {
                    // NC2/CM2 — authority FIRST: deny before any memory
                    // access, allocation, parse, or solver construction.
                    if !grants_for_z3.z3_allowed() {
                        crate::trace::shim_exit("z3_check", pack_error(403), 0);
                        return pack_error(403);
                    }
                    // NC3/CM3 — bound the query length before reading.
                    if query_len < 0 {
                        return pack_error(400);
                    }
                    if query_len as usize > MAX_Z3_QUERY_BYTES {
                        return pack_error(413);
                    }
                    let (memory, _bump_global) = match get_guest_memory_and_bump(&mut caller) {
                        Ok(exports) => exports,
                        Err(_) => return pack_error(500),
                    };
                    // read_guest_string_limited bounds-checks ptr/len and validates
                    // UTF-8; any failure → malformed (NC3).
                    let query = match read_guest_string_limited(
                        &memory,
                        &caller,
                        query_ptr,
                        query_len,
                        MAX_Z3_QUERY_BYTES,
                        "z3 query",
                    ) {
                        Ok(s) => s,
                        Err(err) => return pack_error(err.code),
                    };
                    // NC3 — z3's `Solver::from_string` does
                    // `CString::new(src).unwrap()`, which PANICS on an
                    // interior NUL. Reject NUL before handing it over.
                    if query.as_bytes().contains(&0) {
                        return pack_error(400);
                    }
                    z3_solve_smtlib2(&query)
                },
            )
            .map_err(wrap_err)?;
    }

    Ok(())
}

/// Phase 5a-2 / I26: cap on `random_bytes(out_len)`. Prevents adversarial
/// tools from burning fuel on a 1 GB random allocation.
const MAX_RANDOM_BYTES: usize = 64 * 1024;

/// Marsaglia xorshift64* with multiplier `0x2545F4914F6CDD1D`.
/// Algorithm constants are PINNED — see [`crate::grants::RandomGrant::Seeded`].
/// `state` is the per-execution PRNG state (kept on `EphemeralData`);
/// each call advances it. `buf` is filled with the output bytes,
/// little-endian per u64 produced.
fn fill_seeded(state: &mut u64, buf: &mut [u8]) {
    let mut i = 0;
    while i < buf.len() {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        let out = state.wrapping_mul(0x2545_F491_4F6C_DD1D);
        let take = core::cmp::min(8, buf.len() - i);
        for b in 0..take {
            buf[i + b] = (out >> (b * 8)) as u8;
        }
        i += take;
    }
}

// ── Self-hosting Cap<Z3> solver helpers (feature-gated) ─────────────────

/// Per-call Z3 resource limit (conflicts/decisions), pinned for determinism
/// (NC4) — mirrors sigil-compiler's `Z3_RLIMIT`. An rlimit (solver fuel),
/// NOT a wall-clock timeout, so the verdict is machine-speed-independent.
#[cfg(feature = "solver")]
const Z3_RUNTIME_RLIMIT: u32 = 1_000_000;

/// Cap on an SMT-LIB2 query handed to `z3_check` (1 MiB). Bounds host
/// memory + parse cost (NC3); larger queries are rejected with -413.
#[cfg(feature = "solver")]
const MAX_Z3_QUERY_BYTES: usize = 1024 * 1024;

/// Run an SMT-LIB2 query through a fresh, isolated Z3 solver and return the
/// packed verdict. SOUNDNESS (NC1): a non-{Sat,Unsat} outcome — Unknown,
/// parse failure, or zero parsed assertions — NEVER maps to sat(1)/unsat(0);
/// each maps to a distinct negative code. Determinism (NC4): a fresh
/// `Context` per call, rlimit-bounded, no wall-clock timeout.
#[cfg(feature = "solver")]
fn z3_solve_smtlib2(query: &str) -> i64 {
    z3_solve_smtlib2_with_rlimit(query, Z3_RUNTIME_RLIMIT)
}

/// Core solve with an explicit rlimit. The rlimit seam exists so a unit test
/// can force `Unknown` via a starved budget and confirm it maps to -408,
/// never 0/1.
#[cfg(feature = "solver")]
fn z3_solve_smtlib2_with_rlimit(query: &str, rlimit: u32) -> i64 {
    let cfg = z3::Config::new();
    let ctx = z3::Context::new(&cfg);
    let solver = z3::Solver::new(&ctx);
    let mut params = z3::Params::new(&ctx);
    params.set_u32("rlimit", rlimit);
    solver.set_params(&params);

    // `from_string` returns () and SWALLOWS SMT-LIB2 parse errors (the
    // Context installs a null error handler), so it cannot be trusted to
    // signal failure on its own.
    solver.from_string(query);

    // MI3/CM1 — parse-error gate: if nothing parsed into an assertion, the
    // query was malformed or empty. Refuse to let `check()` on an empty
    // solver return a spurious Sat. Reject as malformed — NEVER 0/1.
    if solver.get_assertions().is_empty() {
        return pack_error(400);
    }

    // Sanctioned carve-out (census-pinned by the compiler's
    // tests/z3_guard_fences.rs): this is the RUNTIME Cap<Z3> shim — it
    // solves queries handed to it by running SIGIL programs under an
    // explicit Z3 grant, a different trust domain from the compiler's
    // verifier. The compile-time fragment guard's allowlist does not
    // govern it; its soundness contract is NC1 (non-verdict outcomes
    // are never read as sat/unsat — see docs/z3-runtime-capability.md).
    #[allow(clippy::disallowed_methods)]
    let result = solver.check();
    match result {
        z3::SatResult::Sat => 1,
        z3::SatResult::Unsat => 0,
        // NC1 — "don't know" is never "proven": a distinct negative code.
        z3::SatResult::Unknown => pack_error(408),
    }
}

#[cfg(all(test, feature = "solver"))]
mod z3_shim_tests {
    use super::*;

    #[test]
    fn sat_query_returns_1() {
        assert_eq!(z3_solve_smtlib2("(declare-const x Int)(assert (> x 0))"), 1);
    }

    #[test]
    fn unsat_query_returns_0() {
        assert_eq!(
            z3_solve_smtlib2("(declare-const x Int)(assert (> x 0))(assert (< x 0))"),
            0
        );
    }

    #[test]
    fn empty_query_is_malformed_not_sat() {
        // NC1: zero parsed assertions must NEVER read as sat(1).
        assert_eq!(z3_solve_smtlib2(""), pack_error(400));
    }

    #[test]
    fn garbage_query_is_malformed_not_sat() {
        // NC1: a query Z3 cannot parse adds no assertions → -400, not 1.
        assert_eq!(
            z3_solve_smtlib2("this is not smtlib2 at all"),
            pack_error(400)
        );
    }

    #[test]
    fn rlimit_starved_returns_unknown_not_verdict() {
        // NC1: Unknown (forced by rlimit=1 on a nonlinear query) maps to
        // -408, never 0/1.
        let hard = "(declare-const x Int)(declare-const y Int)(declare-const z Int)\
                    (assert (> x 0))(assert (> y 0))(assert (> z 0))\
                    (assert (= (+ (* x x x) (* y y y)) (* z z z)))";
        assert_eq!(z3_solve_smtlib2_with_rlimit(hard, 1), pack_error(408));
    }

    #[test]
    fn deterministic_same_query_same_verdict() {
        // NC4: same query ⇒ same verdict (fresh isolated Context per call,
        // rlimit-bounded, no wall-clock dependence).
        let sat = "(declare-const x Int)(assert (> x 5))";
        assert_eq!(z3_solve_smtlib2(sat), z3_solve_smtlib2(sat));
        let unsat = "(declare-const x Int)(assert (> x 0))(assert (< x 0))";
        assert_eq!(z3_solve_smtlib2(unsat), z3_solve_smtlib2(unsat));
    }
}

fn find_tool_main(
    instance: &wasmtime::Instance,
    store: &mut Store<EphemeralData>,
) -> Option<wasmtime::Func> {
    // Try the canonical name first.
    if let Some(f) = instance.get_func(&mut *store, "tool__tool_main") {
        return Some(f);
    }
    // Search all exports for any name containing "tool_main".
    for export in instance.exports(&mut *store) {
        if export.name().contains("tool_main")
            && let Some(f) = export.into_func()
        {
            return Some(f);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use std::{
        io::{Read, Write},
        net::TcpListener,
        thread,
    };

    use sigil_compiler::compile_tool;
    use wasmtime::Val;

    use super::*;
    use crate::grants::{NetGrant, SecretGrant};

    /// SELF-4: a budget above the 1 GiB ceiling is rejected LOUDLY (never clamped), and a
    /// raised budget actually lifts the wall a default-sandbox allocation would hit.
    #[test]
    fn memory_budget_ceiling_and_raise() {
        // ceiling: reject loudly before any execution.
        let compiled = compile_tool(
            // `pub`: since the export-hygiene rule only externally callable functions
            // are exported, and this test needs the entry point, not the wall alone.
            "module t;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0; }\n",
        )
        .expect("tool compiles");
        let err = execute_ephemeral_with_memory_budget(
            &compiled.wasm,
            b"",
            1_000_000,
            MAX_MEMORY_BUDGET_BYTES + 1,
            &IoGrants::none(),
        )
        .expect_err("a budget above the ceiling must be rejected");
        assert!(
            format!("{err:?}").contains("ceiling"),
            "the rejection names the ceiling: {err:?}"
        );

        // raise: a 20 MB input exceeds the 16 MB default but fits a 64 MB budget.
        let big_input = vec![b' '; 20 * 1024 * 1024];
        let default_err =
            execute_ephemeral(&compiled.wasm, &big_input, 1_000_000, &IoGrants::none())
                .expect_err("the default sandbox must reject a 20 MB input");
        assert!(
            format!("{default_err:?}").contains("memory limit"),
            "default rejection is the memory wall: {default_err:?}"
        );
        execute_ephemeral_with_memory_budget(
            &compiled.wasm,
            &big_input,
            1_000_000,
            64 * 1024 * 1024,
            &IoGrants::none(),
        )
        .expect("the raised budget admits the same input");
    }

    /// The declared ephemeral profile and the real linker must agree name for name and type
    /// for type, in both directions; a `ffi` import added to one side without the other fails
    /// here, not at a user's first compile against the profile.
    #[test]
    fn ephemeral_profile_declares_exactly_the_linked_ffi_imports() {
        let mut config = wasmtime::Config::new();
        config.consume_fuel(true);
        let engine = wasmtime::Engine::new(&config).expect("engine");
        let mut linker = wasmtime::Linker::new(&engine);
        link_sigil_imports(&mut linker).expect("sigil imports");
        link_ffi_imports(&mut linker, &IoGrants::none()).expect("ffi imports");
        let mut store = wasmtime::Store::new(&engine, store_data(1, &IoGrants::none(), 1 << 20));
        let items: Vec<(String, String, wasmtime::Extern)> = linker
            .iter(&mut store)
            .map(|(module, name, ext)| (module.to_owned(), name.to_owned(), ext))
            .collect();
        let mut linked = std::collections::BTreeMap::new();
        for (module, name, ext) in items {
            if module != "ffi" {
                continue;
            }
            let func = ext.into_func().expect("ffi imports are functions");
            let ty = func.ty(&store);
            linked.insert(
                name,
                (
                    ty.params().map(|t| format!("{t}")).collect::<Vec<_>>(),
                    ty.results().map(|t| format!("{t}")).collect::<Vec<_>>(),
                ),
            );
        }
        let profile = crate::ephemeral_profile::ephemeral_host_profile();
        let declared: std::collections::BTreeMap<String, (Vec<String>, Vec<String>)> = profile
            .operations()
            .iter()
            .map(|op| {
                assert_eq!(op.module, "ffi");
                let ty = |v: &sigil_abi::host_contract::HostValueContract| {
                    format!("{:?}", v.ty).to_lowercase()
                };
                (
                    op.name.clone(),
                    (
                        op.params.iter().map(ty).collect(),
                        op.results.iter().map(ty).collect(),
                    ),
                )
            })
            .collect();
        assert_eq!(
            declared, linked,
            "the ephemeral profile must declare exactly the linker's ffi inventory"
        );
        assert!(
            !linked.is_empty(),
            "the inventory census must not be vacuous"
        );
    }

    /// A tool compiled against the ephemeral profile runs here, and one compiled against any
    /// other profile is refused before instantiation (fail closed).
    #[test]
    fn profile_bound_tools_run_only_under_the_matching_host() {
        use sigil_compiler::{CompilerContext, compile_tool_with_context};
        // Host-conditioned host call: the second read happens only when the first succeeded,
        // which the legacy Public-occurrence context refuses and the ephemeral profile admits.
        let source = "#[ring(outer)] #[trusted] module t;\n\
            extern \"C\" fn crypto_sha256(ptr: i32, len: i32) -> i64 ! { FFI, Unsafe };\n\
            pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { FFI, Unsafe } {\n\
                let first: i64 @Internal = crypto_sha256(0, 0);\n\
                if first < 0 { return first; } else { let second: i64 @Internal = crypto_sha256(0, 0); return 0; }\n\
            }\n";
        let legacy = sigil_compiler::compile_tool(source);
        assert!(
            legacy.is_err(),
            "the legacy context refuses a host call under Internal control"
        );
        let matching =
            CompilerContext::with_host_profile(crate::ephemeral_profile::ephemeral_host_profile());
        let compiled = compile_tool_with_context(source, &matching)
            .expect("the ephemeral profile admits the host-conditioned call");
        let run = execute_ephemeral(&compiled.wasm, b"", 1_000_000, &IoGrants::none())
            .expect("a tool bound to the ephemeral profile runs under the ephemeral host");
        assert_eq!(run.output.len(), 0);
        let other = CompilerContext::with_host_profile(
            sigil_abi::host_contract::HostContractProfile::new(
                "some-other-host".to_owned(),
                1,
                Vec::new(),
                crate::ephemeral_profile::ephemeral_host_profile()
                    .operations()
                    .to_vec(),
            )
            .expect("a differently named copy of the profile is valid"),
        );
        let foreign = compile_tool_with_context(source, &other)
            .expect("the other host's profile also admits the call");
        let refused = execute_ephemeral(&foreign.wasm, b"", 1_000_000, &IoGrants::none())
            .expect_err("a tool bound to another host's profile is refused here");
        assert!(
            format!("{refused:?}").contains("profile"),
            "the refusal names the profile mismatch: {refused:?}"
        );
    }

    fn instantiate_tool(
        source: &str,
        grants: &IoGrants,
    ) -> (Store<EphemeralData>, wasmtime::Instance, u64) {
        let compiled = compile_tool(source).expect("tool source should compile");
        let engine = Engine::default();
        let mut linker = Linker::new(&engine);
        link_sigil_imports(&mut linker).expect("sigil imports should link");
        link_ffi_imports(&mut linker, grants).expect("ffi imports should link");
        let module = Module::new(&engine, &compiled.wasm).expect("wasm should compile");
        let mut store = Store::new(
            &engine,
            store_data(compiled.fuel_budget, grants, MAX_GUEST_MEMORY_BYTES),
        );
        store.limiter(|data| &mut data.limits);
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("tool should instantiate");
        (store, instance, compiled.fuel_budget)
    }

    fn spawn_http_server(
        expected_method: &'static str,
        response_body: &'static [u8],
    ) -> (String, thread::JoinHandle<()>) {
        let listener = TcpListener::bind("127.0.0.1:0").expect("loopback bind should succeed");
        let addr = listener
            .local_addr()
            .expect("listener should have local addr");
        let url = format!("http://{addr}/");
        let handle = thread::spawn(move || {
            let (mut stream, _) = listener.accept().expect("server should accept one request");
            let mut request = Vec::new();
            let mut buf = [0u8; 1024];
            let mut expected_total = None;
            loop {
                let bytes_read = stream.read(&mut buf).expect("server should read request");
                if bytes_read == 0 {
                    break;
                }
                request.extend_from_slice(&buf[..bytes_read]);
                if let Some(header_end) =
                    request.windows(4).position(|window| window == b"\r\n\r\n")
                {
                    let content_length = String::from_utf8_lossy(&request[..header_end])
                        .lines()
                        .find_map(|line| {
                            let (name, value) = line.split_once(':')?;
                            if name.eq_ignore_ascii_case("Content-Length") {
                                value.trim().parse::<usize>().ok()
                            } else {
                                None
                            }
                        })
                        .unwrap_or(0);
                    let total = header_end + 4 + content_length;
                    expected_total = Some(total);
                    if request.len() >= total {
                        break;
                    }
                }
                if let Some(total) = expected_total
                    && request.len() >= total
                {
                    break;
                }
            }
            let request_text = String::from_utf8_lossy(&request);
            assert!(
                request_text.starts_with(expected_method),
                "expected `{expected_method}`, got `{request_text}`"
            );

            let headers = format!(
                "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
                response_body.len()
            );
            stream
                .write_all(headers.as_bytes())
                .expect("server should write headers");
            stream
                .write_all(response_body)
                .expect("server should write body");
        });
        (url, handle)
    }

    #[test]
    fn alloc_import_advances_bump_ptr_for_array_literals() {
        let source = r#"
module tool;
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {
    let data = [1, 2, 3];
    return 0;
}
"#;
        let (mut store, instance, _) = instantiate_tool(source, &IoGrants::none());
        let bump_global = instance
            .get_global(&mut store, "BUMP_PTR")
            .expect("tool should export BUMP_PTR");
        let tool_main = find_tool_main(&instance, &mut store).expect("tool_main should exist");

        let before = bump_global.get(&mut store).unwrap_i32();
        let mut results = [Val::I64(0)];
        tool_main
            .call(&mut store, &[Val::I32(0), Val::I32(0)], &mut results)
            .expect("tool should execute");
        let after = bump_global.get(&mut store).unwrap_i32();

        assert!(
            after > before,
            "array literal allocation should advance BUMP_PTR ({before} -> {after})"
        );
    }

    /// DEF-2a PR-5: the empirical reclamation proof. The SAME allocation
    /// (`[1, 2, 3]`) advances `BUMP_PTR` when done at function scope, but leaves it
    /// UNCHANGED when wrapped in a `region {}` — because `RegionEnd` rewinds the cursor
    /// to its pre-region value (`global.get 0; local.set save` … `local.get save;
    /// global.set 0`). This is the "memory is actually reclaimed" witness the old no-op
    /// stub never had.
    #[test]
    fn region_reclaims_its_allocations_at_block_exit() {
        // Control: a bare allocation persists past tool_main (cursor advances).
        let bare = r#"
module tool;
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {
    let data = [1, 2, 3];
    return 0;
}
"#;
        // Region-wrapped: the same allocation is reclaimed at block exit (cursor restored).
        let regioned = r#"
module tool;
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {
    region scratch(4096) {
        let data = [1, 2, 3];
    };
    return 0;
}
"#;

        let run = |src: &str| -> (i32, i32) {
            let (mut store, instance, _) = instantiate_tool(src, &IoGrants::none());
            let bump = instance
                .get_global(&mut store, "BUMP_PTR")
                .expect("tool should export BUMP_PTR");
            let tool_main = find_tool_main(&instance, &mut store).expect("tool_main should exist");
            let before = bump.get(&mut store).unwrap_i32();
            let mut results = [Val::I64(0)];
            tool_main
                .call(&mut store, &[Val::I32(0), Val::I32(0)], &mut results)
                .expect("tool should execute");
            let after = bump.get(&mut store).unwrap_i32();
            (before, after)
        };

        let (bare_before, bare_after) = run(bare);
        assert!(
            bare_after > bare_before,
            "control: a bare allocation must advance BUMP_PTR ({bare_before} -> {bare_after})"
        );

        let (reg_before, reg_after) = run(regioned);
        assert_eq!(
            reg_after, reg_before,
            "a region must reclaim its allocations: BUMP_PTR should return to its \
             pre-region value ({reg_before} -> {reg_after})"
        );
    }

    /// DEF-2a PR-5: two sequential regions REUSE the same memory span. Each allocates
    /// the same amount and reclaims on exit, so after both run `BUMP_PTR` is back at its
    /// start — proving the second region allocated over the (reclaimed) first, rather
    /// than stacking on top of it (which would leave the cursor at start + 2×size).
    #[test]
    fn sequential_regions_reuse_the_same_span() {
        let src = r#"
module tool;
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {
    region first(4096) {
        let a = [1, 2, 3];
    };
    region second(4096) {
        let b = [4, 5, 6];
    };
    return 0;
}
"#;
        let (mut store, instance, _) = instantiate_tool(src, &IoGrants::none());
        let bump = instance
            .get_global(&mut store, "BUMP_PTR")
            .expect("tool should export BUMP_PTR");
        let tool_main = find_tool_main(&instance, &mut store).expect("tool_main should exist");
        let before = bump.get(&mut store).unwrap_i32();
        let mut results = [Val::I64(0)];
        tool_main
            .call(&mut store, &[Val::I32(0), Val::I32(0)], &mut results)
            .expect("tool should execute");
        let after = bump.get(&mut store).unwrap_i32();
        assert_eq!(
            after, before,
            "two sequential regions should both reclaim (second reuses the first's span): \
             BUMP_PTR {before} -> {after}"
        );
    }

    /// DEF-2a PR-5, NC-R6 fail-fast: reclamation can never coexist with a slipped
    /// escape. A program that lets a region-allocated value escape MUST be rejected at
    /// compile time (T254) — so no reclaiming wasm is ever emitted for it.
    #[test]
    fn region_escape_is_rejected_before_codegen() {
        let escaping = r#"
module tool;
record Point { x: i64, y: i64 }
fn sink(p: Point) -> i64 { return p.x; }
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {
    region scratch(64) {
        let p: Point = Point { x: 1, y: 2 };
        let _r: i64 = sink(p);
    };
    return 0;
}
"#;
        let err = compile_tool(escaping).expect_err("region escape must be rejected");
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        assert!(
            codes.contains(&"T254"),
            "region escape must be rejected with T254, got {codes:?}"
        );
    }

    /// DEF-2a PR-6: the `(LIMIT)` exit-check is enforced. The SAME region body — a
    /// 5-element array — runs cleanly under a generous budget but TRAPS under a tiny one,
    /// because `RegionEnd` checks `(BUMP_PTR - save) <= limit` before reclaiming and
    /// executes `unreachable` when the region's net allocation overran its declared
    /// budget. The two cases differ only in the limit, isolating the trap to the LIMIT
    /// check (not the allocation itself, which fits in memory either way).
    #[test]
    fn region_over_limit_traps_within_limit_runs() {
        let within = r#"
module tool;
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {
    region big(4096) {
        let data = [1, 2, 3, 4, 5];
    };
    return 0;
}
"#;
        let over = r#"
module tool;
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {
    region tiny(8) {
        let data = [1, 2, 3, 4, 5];
    };
    return 0;
}
"#;

        let run = |src: &str| -> Result<(), ()> {
            let (mut store, instance, _) = instantiate_tool(src, &IoGrants::none());
            let tool_main = find_tool_main(&instance, &mut store).expect("tool_main should exist");
            let mut results = [Val::I64(0)];
            tool_main
                .call(&mut store, &[Val::I32(0), Val::I32(0)], &mut results)
                .map(|_| ())
                .map_err(|_| ())
        };

        assert!(
            run(within).is_ok(),
            "a region whose allocation fits its declared budget must run cleanly"
        );
        assert!(
            run(over).is_err(),
            "a region whose allocation overruns its declared budget must trap"
        );
    }

    #[test]
    fn http_get_tool_returns_response_body() {
        let source = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn http_get(url: i32, url_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { NetIO, Alloc, FFI, Unsafe } {
    return http_get(input_ptr, input_len);
}
"#;
        let (url, server) = spawn_http_server("GET ", b"hello from host");
        let grants = IoGrants {
            net: vec![NetGrant {
                host_pattern: "127.0.0.1".into(),
                methods: vec![HttpMethod::Get],
            }],
            ..Default::default()
        };

        let (_, _, fuel_budget) = instantiate_tool(source, &grants);
        let compiled = compile_tool(source).expect("http get tool should compile");
        let result = execute_ephemeral(&compiled.wasm, url.as_bytes(), fuel_budget, &grants)
            .expect("http get tool should execute");
        server.join().expect("server thread should finish");

        assert_eq!(result.output, b"hello from host");
    }

    #[test]
    fn http_post_tool_returns_response_body() {
        let source = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn http_post(url: i32, url_len: i32, body_ptr: i32, body_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { NetIO, Alloc, FFI, Unsafe } {
    return http_post(input_ptr, input_len, input_ptr, input_len);
}
"#;
        let (url, server) = spawn_http_server("POST ", b"posted");
        let grants = IoGrants {
            net: vec![NetGrant {
                host_pattern: "127.0.0.1".into(),
                methods: vec![HttpMethod::Post],
            }],
            ..Default::default()
        };

        let (_, _, fuel_budget) = instantiate_tool(source, &grants);
        let compiled = compile_tool(source).expect("http post tool should compile");
        let result = execute_ephemeral(&compiled.wasm, url.as_bytes(), fuel_budget, &grants)
            .expect("http post tool should execute");
        server.join().expect("server thread should finish");

        assert_eq!(result.output, b"posted");
    }

    /// A one-shot server that answers any request with a 302 to `location`.
    fn spawn_redirect_server(location: String) -> (String, thread::JoinHandle<()>) {
        let listener = TcpListener::bind("127.0.0.1:0").expect("loopback bind should succeed");
        let addr = listener
            .local_addr()
            .expect("listener should have local addr");
        let url = format!("http://{addr}/");
        let handle = thread::spawn(move || {
            let (mut stream, _) = listener
                .accept()
                .expect("redirector should accept one request");
            let mut buf = [0u8; 1024];
            let mut request = Vec::new();
            loop {
                let n = stream
                    .read(&mut buf)
                    .expect("redirector should read request");
                if n == 0 {
                    break;
                }
                request.extend_from_slice(&buf[..n]);
                if request.windows(4).any(|w| w == b"\r\n\r\n") {
                    break;
                }
            }
            let response = format!(
                "HTTP/1.1 302 Found\r\nLocation: {location}\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"
            );
            stream
                .write_all(response.as_bytes())
                .expect("redirector should write 302");
        });
        (url, handle)
    }

    #[test]
    fn http_get_follows_same_host_redirect_after_revalidation() {
        // The real target (granted host) serves the body.
        let (target_url, target_server) = spawn_http_server("GET ", b"followed-body");
        // The redirector (same, granted host) 302s to the target. With the fix,
        // the agent does NOT auto-follow; `http_fetch` reads the Location,
        // re-validates it against the grant (127.0.0.1 is granted), and follows.
        let (start_url, redirect_server) = spawn_redirect_server(target_url);
        let source = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn http_get(url: i32, url_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { NetIO, Alloc, FFI, Unsafe } {
    return http_get(input_ptr, input_len);
}
"#;
        let grants = IoGrants {
            net: vec![NetGrant {
                host_pattern: "127.0.0.1".into(),
                methods: vec![HttpMethod::Get],
            }],
            ..Default::default()
        };

        let (_, _, fuel_budget) = instantiate_tool(source, &grants);
        let compiled = compile_tool(source).expect("redirect tool should compile");
        let result = execute_ephemeral(&compiled.wasm, start_url.as_bytes(), fuel_budget, &grants)
            .expect("redirect tool should execute");
        redirect_server
            .join()
            .expect("redirector thread should finish");
        target_server.join().expect("target thread should finish");

        assert_eq!(
            result.output, b"followed-body",
            "a same-host redirect must be followed after re-validation"
        );
    }

    #[test]
    fn hostile_wasm_infinite_loop_is_bounded_by_fuel_backstop() {
        // A hand-written module that loops forever WITHOUT ever calling the
        // cooperative SIGIL fuel host import. Before the wasmtime fuel backstop
        // the engine had no fuel/epoch limit, so this ran until the process was
        // killed. Now it traps once the injected fuel cap is spent. The test
        // completing at all (rather than hanging the suite) is the core
        // assertion — an unbounded engine would never return here.
        let module = wat::parse_str(
            r#"
            (module
              (memory (export "memory") 1)
              (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
              (func (export "tool__tool_main") (param i32 i32) (result i64)
                (loop $l (br $l))
                (i64.const 0)))
            "#,
        )
        .expect("hostile WAT should compile");

        // Small fuel cap so the loop trips the backstop quickly.
        let result =
            execute_ephemeral_with_wasm_fuel(&module, b"", 1_000, 200_000, &IoGrants::none());
        match result {
            Err(ToolError::Trapped { .. }) => {}
            other => panic!("infinite loop must trap on the fuel backstop, got {other:?}"),
        }
    }

    #[test]
    fn well_behaved_wasm_runs_under_the_fuel_backstop() {
        // A trivial module that returns immediately consumes negligible fuel and
        // must NOT be affected by the backstop.
        let module = wat::parse_str(
            r#"
            (module
              (memory (export "memory") 1)
              (global (export "BUMP_PTR") (mut i32) (i32.const 1024))
              (func (export "tool__tool_main") (param i32 i32) (result i64)
                (i64.const 0)))
            "#,
        )
        .expect("trivial WAT should compile");

        let result =
            execute_ephemeral_with_wasm_fuel(&module, b"", 1_000, 200_000, &IoGrants::none());
        assert!(
            result.is_ok(),
            "a tool that returns immediately must run under the backstop: {result:?}"
        );
    }

    /// Spawn a one-request server that extracts the `x-echo` request header and
    /// returns its value as the response body — proving the outbound header
    /// actually crossed the wire (not just that the shim accepted it).
    fn spawn_header_echo_server() -> (String, thread::JoinHandle<()>) {
        let listener = TcpListener::bind("127.0.0.1:0").expect("loopback bind should succeed");
        let addr = listener
            .local_addr()
            .expect("listener should have local addr");
        let url = format!("http://{addr}/");
        let handle = thread::spawn(move || {
            let (mut stream, _) = listener.accept().expect("server should accept one request");
            let mut request = Vec::new();
            let mut buf = [0u8; 1024];
            loop {
                let bytes_read = stream.read(&mut buf).expect("server should read request");
                if bytes_read == 0 {
                    break;
                }
                request.extend_from_slice(&buf[..bytes_read]);
                if request.windows(4).any(|w| w == b"\r\n\r\n") {
                    break;
                }
            }
            let echoed = String::from_utf8_lossy(&request)
                .lines()
                .find_map(|line| {
                    let (name, value) = line.split_once(':')?;
                    name.eq_ignore_ascii_case("x-echo")
                        .then(|| value.trim().to_string())
                })
                .unwrap_or_else(|| "MISSING".to_string());
            let response = format!(
                "HTTP/1.1 200 OK\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}",
                echoed.len(),
                echoed
            );
            stream
                .write_all(response.as_bytes())
                .expect("server should write response");
        });
        (url, handle)
    }

    #[test]
    fn http_post_hdrs_tool_sends_request_headers() {
        // Input layout: '<url>|<header blob>'. The tool splits on the first '|',
        // POSTs an empty body with the caller-supplied headers, and returns the
        // response body — which the echo server sets to the received x-echo value.
        let source = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn http_post_hdrs(url: i32, url_len: i32, body_ptr: i32, body_len: i32, hdrs_ptr: i32, hdrs_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { NetIO, Alloc, FFI, Unsafe } {
    let mut split = input_len;
    let mut i = input_len - input_len;
    while i < input_len {
        if split == input_len {
            if load8(input_ptr + i) == 124 {
                split = i;
            }
        }
        i = i + 1;
    }
    let hdrs_ptr: i32 = input_ptr + split + 1;
    let hdrs_len: i32 = input_len - split - 1;
    return http_post_hdrs(input_ptr, split, input_ptr, split - split, hdrs_ptr, hdrs_len);
}
"#;
        let (url, server) = spawn_header_echo_server();
        let grants = IoGrants {
            net: vec![NetGrant {
                host_pattern: "127.0.0.1".into(),
                methods: vec![HttpMethod::Post],
            }],
            ..Default::default()
        };

        let input = format!("{url}|x-echo: sigil-was-here\nx-other: 1");
        let (_, _, fuel_budget) = instantiate_tool(source, &grants);
        let compiled = compile_tool(source).expect("http post hdrs tool should compile");
        let result = execute_ephemeral(&compiled.wasm, input.as_bytes(), fuel_budget, &grants)
            .expect("http post hdrs tool should execute");
        server.join().expect("server thread should finish");

        assert_eq!(result.output, b"sigil-was-here");
    }

    #[test]
    fn http_post_hdrs_rejects_oversized_header_blob() {
        // The tool claims a >8 KB header blob; the shim must refuse with -431
        // BEFORE dereferencing it. Returning the shim result directly surfaces
        // the negative code as a "tool returned error (431)" trap (same
        // pattern as the kv shim tests).
        let source = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn http_post_hdrs(url: i32, url_len: i32, body_ptr: i32, body_len: i32, hdrs_ptr: i32, hdrs_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { NetIO, Alloc, FFI, Unsafe } {
    let zero = input_len - input_len;
    return http_post_hdrs(input_ptr, input_len, input_ptr, zero, input_ptr, zero + 9000);
}
"#;
        let grants = IoGrants {
            net: vec![NetGrant {
                host_pattern: "127.0.0.1".into(),
                methods: vec![HttpMethod::Post],
            }],
            ..Default::default()
        };

        let (_, _, fuel_budget) = instantiate_tool(source, &grants);
        let compiled = compile_tool(source).expect("cap test tool should compile");
        let err = execute_ephemeral(&compiled.wasm, b"http://127.0.0.1:1/", fuel_budget, &grants)
            .expect_err("oversized header blob should be rejected");

        match err {
            ToolError::Trapped { message } => assert!(
                message.contains("tool returned error (431)"),
                "expected the -431 header-cap code, got: {message}"
            ),
            other => panic!("expected a trapped -431, got: {other:?}"),
        }
    }

    // Input layout for the post_secret tests: '<url>|<header blob>'. The tool
    // POSTs an empty body with the placeholder header blob; the host
    // substitutes {{secret:NAME}} before sending. The echo server returns the
    // received x-echo header value, proving the SUBSTITUTED secret crossed the
    // wire — while the guest only ever held the placeholder.
    const POST_SECRET_TOOL: &str = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn http_post_secret(url: i32, url_len: i32, body_ptr: i32, body_len: i32, hdrs_ptr: i32, hdrs_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { NetIO, Alloc, FFI, Unsafe } {
    let mut split = input_len;
    let mut i = input_len - input_len;
    while i < input_len {
        if split == input_len {
            if load8(input_ptr + i) == 124 {
                split = i;
            }
        }
        i = i + 1;
    }
    let hdrs_ptr: i32 = input_ptr + split + 1;
    let hdrs_len: i32 = input_len - split - 1;
    return http_post_secret(input_ptr, split, input_ptr, split - split, hdrs_ptr, hdrs_len);
}
"#;

    #[test]
    fn http_post_secret_substitutes_granted_secret_host_side() {
        let (url, server) = spawn_header_echo_server();
        let grants = IoGrants {
            net: vec![NetGrant {
                host_pattern: "127.0.0.1".into(),
                methods: vec![HttpMethod::Post],
            }],
            secret: vec![SecretGrant {
                name: "apikey".into(),
                value: b"sk-real-SECRET-value".to_vec(),
            }],
            ..Default::default()
        };
        // The guest blob contains only the PLACEHOLDER.
        let input = format!("{url}|x-echo: {{{{secret:apikey}}}}");
        let (_, _, fuel_budget) = instantiate_tool(POST_SECRET_TOOL, &grants);
        let compiled = compile_tool(POST_SECRET_TOOL).expect("post_secret tool should compile");
        let result = execute_ephemeral(&compiled.wasm, input.as_bytes(), fuel_budget, &grants)
            .expect("post_secret tool should execute");
        server.join().expect("server thread should finish");
        // The server received the SUBSTITUTED value — the host injected it.
        assert_eq!(result.output, b"sk-real-SECRET-value");
        // And the substituted secret is NOT anywhere in the guest input bytes.
        assert!(
            !input
                .as_bytes()
                .windows(20)
                .any(|w| w == b"sk-real-SECRET-value")
        );
    }

    #[test]
    fn http_post_secret_denies_ungranted_placeholder() {
        // A placeholder naming a secret with no grant is -403 — fail closed.
        let grants = IoGrants {
            net: vec![NetGrant {
                host_pattern: "127.0.0.1".into(),
                methods: vec![HttpMethod::Post],
            }],
            // no secret grant at all
            ..Default::default()
        };
        let input = "http://127.0.0.1:1/|x-echo: {{secret:apikey}}";
        let (_, _, fuel_budget) = instantiate_tool(POST_SECRET_TOOL, &grants);
        let compiled = compile_tool(POST_SECRET_TOOL).expect("tool should compile");
        let err = execute_ephemeral(&compiled.wasm, input.as_bytes(), fuel_budget, &grants)
            .expect_err("ungranted placeholder should be denied");
        match err {
            ToolError::Trapped { message } => assert!(
                message.contains("tool returned error (403)"),
                "expected -403 for ungranted secret, got: {message}"
            ),
            other => panic!("expected a trapped -403, got: {other:?}"),
        }
    }

    #[test]
    fn http_post_secret_unterminated_placeholder_is_400() {
        let grants = IoGrants {
            net: vec![NetGrant {
                host_pattern: "127.0.0.1".into(),
                methods: vec![HttpMethod::Post],
            }],
            secret: vec![SecretGrant {
                name: "apikey".into(),
                value: b"x".to_vec(),
            }],
            ..Default::default()
        };
        let input = "http://127.0.0.1:1/|x-echo: {{secret:apikey";
        let (_, _, fuel_budget) = instantiate_tool(POST_SECRET_TOOL, &grants);
        let compiled = compile_tool(POST_SECRET_TOOL).expect("tool should compile");
        let err = execute_ephemeral(&compiled.wasm, input.as_bytes(), fuel_budget, &grants)
            .expect_err("unterminated placeholder should be rejected");
        match err {
            ToolError::Trapped { message } => assert!(
                message.contains("tool returned error (400)"),
                "expected -400 for unterminated placeholder, got: {message}"
            ),
            other => panic!("expected a trapped -400, got: {other:?}"),
        }
    }

    #[test]
    fn substitute_secrets_unit() {
        let grants = IoGrants {
            secret: vec![
                SecretGrant {
                    name: "k".into(),
                    value: b"KV".to_vec(),
                },
                SecretGrant {
                    name: "j".into(),
                    value: b"JV".to_vec(),
                },
            ],
            ..Default::default()
        };
        // multiple placeholders, literal text preserved, single-pass
        assert_eq!(
            substitute_secrets("a: {{secret:k}}\nb: {{secret:j}} tail", &grants).unwrap(),
            "a: KV\nb: JV tail"
        );
        // no placeholders → identity
        assert_eq!(
            substitute_secrets("plain: value", &grants).unwrap(),
            "plain: value"
        );
        // ungranted → 403, unterminated → 400
        assert_eq!(substitute_secrets("{{secret:nope}}", &grants), Err(403));
        assert_eq!(substitute_secrets("{{secret:k", &grants), Err(400));
        // a secret value that itself looks like a placeholder is NOT re-scanned
        let g2 = IoGrants {
            secret: vec![SecretGrant {
                name: "k".into(),
                value: b"{{secret:j}}".to_vec(),
            }],
            ..Default::default()
        };
        assert_eq!(
            substitute_secrets("{{secret:k}}", &g2).unwrap(),
            "{{secret:j}}"
        );
    }

    #[test]
    fn pure_nested_line_scan_regression() {
        let source = r#"
module tool;

fn append_segment(
    out_ptr: i64,
    out_len_in: i64,
    file_ptr: i64,
    start: i64,
    end: i64,
) -> i64 ! {} {
    let mut out_len = out_len_in;
    let mut i = start;

    while i < end {
        let b = load8(file_ptr + i);
        store8(out_ptr + out_len, b);
        out_len = out_len + 1;
        i = i + 1;
    }

    return out_len;
}

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let out_ptr = alloc(input_len);
    let mut out_len = 0;
    let mut line_start = 0;
    let mut line_matched = 0;
    let mut matched_count = 0;
    let mut i = 0;

    while i < input_len {
        let b = load8(input_ptr + i);

        if b == 10 {
            if line_matched == 1 {
                out_len = append_segment(out_ptr, out_len, input_ptr, line_start, i + 1);
            } else {
            }
            line_start = i + 1;
            line_matched = 0;
            matched_count = 0;
        } else {
            if line_matched == 0 {
                if matched_count == 0 {
                    if b == 69 {
                        matched_count = 1;
                    } else {
                    }
                } else {
                    if matched_count == 1 {
                        if b == 82 {
                            matched_count = 2;
                        } else {
                            if b == 69 {
                                matched_count = 1;
                            } else {
                                matched_count = 0;
                            }
                        }
                    } else {
                        if matched_count == 2 {
                            if b == 82 {
                                line_matched = 1;
                            } else {
                                if b == 69 {
                                    matched_count = 1;
                                } else {
                                    matched_count = 0;
                                }
                            }
                        } else {
                        }
                    }
                }
            } else {
            }
        }

        i = i + 1;
    }

    if line_start < input_len {
        if line_matched == 1 {
            out_len = append_segment(out_ptr, out_len, input_ptr, line_start, input_len);
        } else {
        }
    } else {
    }

    return out_ptr * 4294967296 + out_len;
}
"#;
        let compiled = compile_tool(source).expect("nested scan tool should compile");
        let input = b"INFO startup\nERROR disk\nWARN low\nERROR panic\n";
        let result = execute_ephemeral(
            &compiled.wasm,
            input,
            compiled.fuel_budget,
            &IoGrants::none(),
        )
        .expect("nested scan tool should execute");

        assert_eq!(result.output, b"ERROR disk\nERROR panic\n");
    }
}
