//! Resident actor stdin driver (docs/specs/actor-live.md).
//!
//! `serve_loop` streams one input line at a time (never buffering the whole stream), turns
//! each line into a typed `Message`, enqueues it HOST-side via the existing `enqueue_message` public
//! API, adding no actor ABI import, and drains. The loop is a deterministic function
//! of the input stream (no clock/RNG, X-AL7), so restart-as-replay holds.
//!
//! Boring limits (harden-spec): a malformed line is SKIPPED + counted, never a panic (X-AL4d); each
//! line is capped at [`MAX_SERVE_LINE`] bytes so an over-long unterminated line is rejected fail-loud
//! rather than buffered without bound (X-AL4e); on `QueueFull` the loop drains then retries once,
//! else stops fail-loud (X-AL5, never grows).

use std::io::{BufRead, Read};

use sigil_abi::RuntimeTypeSpec;

use crate::{
    actor::ActorId,
    message::Message,
    runtime::{RuntimeError, RuntimeHost, WasmParamKind},
};

/// The maximum length in bytes of a single input line the serve loop accepts. A longer unterminated
/// line is rejected fail-loud rather than buffered without bound (X-AL4e).
pub const MAX_SERVE_LINE: usize = 64 * 1024;

/// Outcome of a [`serve_loop`] run over an input stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ServeStats {
    /// Lines read from the input (including malformed ones).
    pub lines_read: usize,
    /// Well-formed lines turned into a dispatched message.
    pub dispatched: usize,
    /// Lines skipped because they did not parse to the handler's payload type (X-AL4d).
    pub skipped: usize,
    /// Total messages delivered by the drains this loop performed.
    pub delivered: usize,
}

/// Drive a bootstrapped [`RuntimeHost`] as a resident service: read `input` line by line and route
/// each well-formed line to `handler_id` on `receiver` as a typed payload of type `param`, draining
/// up to `drain_limit` messages after each. Returns when the input reaches EOF.
///
/// `param` must be `i64` or `bool` (the scalar shapes a text line can encode); AND the handler's
/// LOWERED wasm param (looked up via `export_name`) must match the payload width — both checked
/// BEFORE any input is read, so an unsupported handler shape fails fast rather than per line.
#[allow(clippy::too_many_arguments)]
pub fn serve_loop<R: BufRead>(
    host: &mut RuntimeHost,
    mut input: R,
    receiver: ActorId,
    handler_id: u32,
    handler_name: &str,
    export_name: &str,
    param: RuntimeTypeSpec,
    drain_limit: usize,
) -> Result<ServeStats, RuntimeError> {
    if !matches!(param, RuntimeTypeSpec::I64 | RuntimeTypeSpec::Bool) {
        return Err(RuntimeError::Wasm {
            message: format!(
                "serve: input handler param must be `i64` or `bool`, found `{param:?}`"
            ),
        });
    }
    // Fail fast at startup: the handler's LOWERED wasm params must match what the dispatch passes.
    // Under the M3 actor-state ABI every handler's FIRST wasm param is the actor's state pointer
    // (`i32`), which `deliver_message` prepends host-side; the DECLARED line param follows. So a
    // serve-able handler lowers to exactly `[i32 state-ptr, <line kind>]`. The line kind must match
    // the payload we encode — `RuntimeTypeSpec` collapses `i32`/`u32`/`i64`/`u64`/`f64` all to `I64`,
    // so a handler declared with `i32`/`u32`/`f64` passes the spec check above but its wasm line
    // param is `i32`/`f64` and a `Val::I64` payload would fail wasmtime's arg-type check on the FIRST
    // line. Reject any mismatch here (before reading input) instead of dying per-line.
    let line_kind = match param {
        RuntimeTypeSpec::Bool => WasmParamKind::I32,
        _ => WasmParamKind::I64,
    };
    let expected = [WasmParamKind::I32, line_kind];
    match host.export_param_kinds(export_name) {
        Some(kinds) if kinds.as_slice() == expected => {}
        Some(kinds) => {
            return Err(RuntimeError::Wasm {
                message: format!(
                    "serve: handler `{handler_name}` lowers to wasm params {kinds:?}, but a serve \
                     handler must be `[i32 state-ptr, {line_kind:?} line]`; only a handler taking \
                     one `i64` or `bool` line value can be served"
                ),
            });
        }
        None => {
            return Err(RuntimeError::Wasm {
                message: format!(
                    "serve: handler export `{export_name}` not found (host not bootstrapped?)"
                ),
            });
        }
    }
    let drain_limit = drain_limit.max(1);
    let mut stats = ServeStats::default();

    // EOF (read_capped_line returns None) ends the loop (MI-AL4a).
    while let Some(bytes) = read_capped_line(&mut input)? {
        stats.lines_read += 1;

        // A line that is not valid UTF-8, or does not parse to the payload type, is SKIPPED +
        // counted (X-AL4d) — a daemon absorbs one bad line rather than aborting.
        let Some(payload) = std::str::from_utf8(&bytes)
            .ok()
            .and_then(|text| encode_line(text.trim(), &param))
        else {
            stats.skipped += 1;
            continue;
        };

        let message = Message {
            sender: None,
            receiver,
            handler: handler_name.to_owned(),
            handler_id,
            payload,
        };

        // Enqueue host-side (X-AL4: no new actor import). On `QueueFull`, drain to make room and
        // retry ONCE; if it is still full the actor produces faster than it drains — stop fail-loud
        // (X-AL5), never grow the queue.
        if let Err(err) = host.enqueue_message(message.clone()) {
            match err {
                RuntimeError::QueueFull { .. } => {
                    stats.delivered += host.drain_messages(drain_limit)?;
                    host.enqueue_message(message)?;
                }
                other => return Err(other),
            }
        }
        stats.dispatched += 1;
        stats.delivered += host.drain_messages(drain_limit)?;
    }

    Ok(stats)
}

/// Read one line (up to and including the newline) into a fresh buffer, bounded at
/// [`MAX_SERVE_LINE`] + 1 bytes. Returns `Ok(None)` at EOF, `Ok(Some(bytes))` for a line (trailing
/// `\n`/`\r\n` stripped), or `Err` if the line exceeds the cap without a newline (X-AL4e).
fn read_capped_line<R: BufRead>(reader: &mut R) -> Result<Option<Vec<u8>>, RuntimeError> {
    let mut buf = Vec::new();
    let read = (&mut *reader)
        .take((MAX_SERVE_LINE + 1) as u64)
        .read_until(b'\n', &mut buf)
        .map_err(|e| RuntimeError::Wasm {
            message: format!("serve: input read failed: {e}"),
        })?;
    if read == 0 {
        return Ok(None);
    }
    // Consuming the whole cap without reaching a newline means the line is over-long.
    if buf.len() > MAX_SERVE_LINE && buf.last() != Some(&b'\n') {
        return Err(RuntimeError::Wasm {
            message: format!("serve: input line exceeds the {MAX_SERVE_LINE}-byte cap"),
        });
    }
    if buf.last() == Some(&b'\n') {
        buf.pop();
        if buf.last() == Some(&b'\r') {
            buf.pop();
        }
    }
    Ok(Some(buf))
}

/// Encode a trimmed text line as the little-endian payload for a scalar handler param, matching the
/// wire format `decode_payload_value` reads back (`i64`=8 bytes, `bool`=4 bytes). Returns `None` if
/// the text does not parse — the caller counts it as a skip.
fn encode_line(text: &str, param: &RuntimeTypeSpec) -> Option<Vec<u8>> {
    match param {
        RuntimeTypeSpec::I64 => text.parse::<i64>().ok().map(|v| v.to_le_bytes().to_vec()),
        RuntimeTypeSpec::Bool => match text {
            "true" | "1" => Some(1i32.to_le_bytes().to_vec()),
            "false" | "0" => Some(0i32.to_le_bytes().to_vec()),
            _ => None,
        },
        _ => None,
    }
}
