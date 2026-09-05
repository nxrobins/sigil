//! Resident actor stdin driver (docs/specs/actor-live.md).
//!
//! `serve_loop` is a persistent, host-side loop that streams one input line at a time, turns each line
//! into a typed `Message`, enqueues it via `enqueue_message` (the existing public API — NO new actor
//! import, X-AL4), and drains. These tests pin: (1) a resident service processes an entire input
//! stream (the wall is down — it does not stop after the boot drain); (2) a malformed line is
//! SKIPPED + counted, never a panic (X-AL4d); (3) the delivered sequence is a deterministic function
//! of the input stream (X-AL7); (4) an over-long unterminated line is rejected fail-loud (X-AL4e).

use std::io::Cursor;

use sigil_abi::RuntimeTypeSpec;
use sigil_runtime::{
    RuntimeActorSpec, RuntimeHandlerSpec, RuntimeHost, RuntimeImportSpec, RuntimeModuleSpec,
};

const BUDGET: u64 = 1_000_000;

/// Entry actor `Main` with a benign `Start` (handler 0) and a `Line(i64)` handler (handler 1) that
/// takes the parsed line value and returns it. One module, one memory.
fn spec() -> RuntimeModuleSpec {
    RuntimeModuleSpec {
        module_name: "al4".to_owned(),
        fuel_budget: BUDGET,
        imports: RuntimeImportSpec::phase_one(),
        actors: vec![RuntimeActorSpec {
            name: "Main".to_owned(),
            actor_type_id: 0,
            is_entry: true,
            init_export: Some("Main__init".to_owned()),
            init_params: vec![],
            handlers: vec![
                RuntimeHandlerSpec {
                    name: "Start".to_owned(),
                    handler_id: 0,
                    export_name: "Main__Start".to_owned(),
                    params: vec![],
                    ret: RuntimeTypeSpec::I64,
                },
                RuntimeHandlerSpec {
                    name: "Line".to_owned(),
                    handler_id: 1,
                    export_name: "Main__Line".to_owned(),
                    params: vec![RuntimeTypeSpec::I64],
                    ret: RuntimeTypeSpec::I64,
                },
            ],
            state_layout: vec![],
            state_size: 0,
            init_replay_safe: false,
        }],
    }
}

fn wat() -> Vec<u8> {
    wat::parse_str(
        r#"(module
  (memory (export "memory") 1)
  (func (export "Main__init") (param i32))
  (func (export "Main__Start") (param i32) (result i64) (i64.const 0))
  (func (export "Main__Line") (param i32 i64) (result i64) (local.get 1)))"#,
    )
    .expect("WAT parses")
}

/// Bootstrap, drain the boot Start, and return a running host + the entry actor id.
fn booted() -> (RuntimeHost, sigil_runtime::ActorId) {
    let s = spec();
    let mut host = RuntimeHost::new(s.fuel_budget);
    let report = host.bootstrap(&s, &wat()).expect("bootstrap runs");
    let entry = report.entry_actor.expect("entry actor");
    host.drain_messages(32).expect("boot drain");
    (host, entry)
}

// ── (1) THE WALL: a resident service processes the whole input stream ─────────────────────────
#[test]
fn serve_processes_the_whole_input_stream() {
    let (mut host, entry) = booted();
    let stats = sigil_runtime::serve_loop(
        &mut host,
        Cursor::new("1\n2\n3\n4\n5\n"),
        entry,
        1,
        "Line",
        "Main__Line",
        RuntimeTypeSpec::I64,
        8,
    )
    .expect("serve loop runs to EOF");
    assert_eq!(
        stats.lines_read, 5,
        "read every line; got {}",
        stats.lines_read
    );
    assert_eq!(
        stats.dispatched, 5,
        "dispatched every well-formed line; got {}",
        stats.dispatched
    );
    assert_eq!(
        stats.delivered, 5,
        "delivered every dispatch; got {}",
        stats.delivered
    );
    assert_eq!(
        stats.skipped, 0,
        "no malformed lines; got {}",
        stats.skipped
    );
}

// ── (2) X-AL4d: a malformed line is SKIPPED + counted, never a panic ──────────────────────────
#[test]
fn malformed_line_is_skipped_not_fatal() {
    let (mut host, entry) = booted();
    // "xyz" and "" are not i64; the daemon absorbs them and keeps serving the rest.
    let stats = sigil_runtime::serve_loop(
        &mut host,
        Cursor::new("10\nxyz\n\n20\n"),
        entry,
        1,
        "Line",
        "Main__Line",
        RuntimeTypeSpec::I64,
        8,
    )
    .expect("a malformed line must not abort the loop");
    assert_eq!(
        stats.lines_read, 4,
        "read all 4 lines; got {}",
        stats.lines_read
    );
    assert_eq!(
        stats.dispatched, 2,
        "only the two i64 lines dispatch; got {}",
        stats.dispatched
    );
    assert_eq!(
        stats.skipped, 2,
        "the two non-i64 lines are skipped; got {}",
        stats.skipped
    );
}

// ── (3) X-AL7: the delivered sequence is a deterministic function of the input stream ─────────
#[test]
fn serve_is_deterministic() {
    let run = || {
        let (mut host, entry) = booted();
        sigil_runtime::serve_loop(
            &mut host,
            Cursor::new("7\n8\n9\n"),
            entry,
            1,
            "Line",
            "Main__Line",
            RuntimeTypeSpec::I64,
            8,
        )
        .expect("serve runs")
    };
    let a = run();
    let b = run();
    assert_eq!(
        (a.lines_read, a.dispatched, a.delivered, a.skipped),
        (b.lines_read, b.dispatched, b.delivered, b.skipped),
        "the same input stream must yield the same stats"
    );
}

// ── (4) X-AL4e: an over-long unterminated line is rejected fail-loud ──────────────────────────
#[test]
fn over_long_line_is_rejected() {
    let (mut host, entry) = booted();
    // A single line far larger than the 64 KiB cap with no newline.
    let huge = "9".repeat(70_000);
    let r = sigil_runtime::serve_loop(
        &mut host,
        Cursor::new(huge),
        entry,
        1,
        "Line",
        "Main__Line",
        RuntimeTypeSpec::I64,
        8,
    );
    assert!(
        r.is_err(),
        "an over-long unterminated line must be rejected fail-loud, not buffered; got {r:?}"
    );
}

// ── (5) FAIL-FAST: an i32/f64-lowered line handler is rejected at STARTUP, not on line 1 ───────
#[test]
fn narrow_param_handler_rejected_at_startup() {
    // The compiler collapses i32/u32/i64/u64/f64 all to RuntimeTypeSpec::I64, so a source `i32`
    // line-handler passes the spec check — but its wasm export param is `i32`, and a Val::I64
    // payload would fail wasmtime's arg-type check on the FIRST line. serve_loop must reject it at
    // STARTUP (before reading input) instead. Here the spec says I64 but the export has an i32 param.
    let s = spec();
    let mut host = RuntimeHost::new(s.fuel_budget);
    let report = host
        .bootstrap(
            &s,
            &wat::parse_str(
                r#"(module
  (memory (export "memory") 1)
  (func (export "Main__init") (param i32))
  (func (export "Main__Start") (param i32) (result i64) (i64.const 0))
  (func (export "Main__Line") (param i32 i32) (result i64) (i64.const 0)))"#,
            )
            .expect("WAT parses"),
        )
        .expect("bootstrap runs");
    let entry = report.entry_actor.expect("entry actor");
    host.drain_messages(32).expect("boot drain");

    // Feed input that WOULD dispatch — the point is the loop errors BEFORE consuming it.
    let err = sigil_runtime::serve_loop(
        &mut host,
        Cursor::new("5\n7\n"),
        entry,
        1,
        "Line",
        "Main__Line",
        RuntimeTypeSpec::I64,
        8,
    )
    .expect_err("an i32-lowered line handler must be rejected at startup");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("lowers to wasm params") && !msg.contains("argument type mismatch"),
        "must be the STARTUP wasm-param rejection, not a per-line dispatch failure; got {msg}"
    );
}
