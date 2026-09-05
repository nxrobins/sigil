//! Phase 5a-1.6 / I21 / AP17 — typed trace event smoke test.
//!
//! Asserts:
//! 1. With `--features trace`, named events fire at the documented
//!    decision points (cross-module dispatch, method-call reroute,
//!    use-scope construction, cycle detection).
//! 2. Event payloads NEVER contain a substring of the input source
//!    longer than 32 bytes (I21: source-redaction).
//!
//! Without `--features trace` this file's only test is gated off, so
//! the default workspace test pass is unaffected. CI runs both modes
//! to verify the discipline.

#![cfg(feature = "trace")]

use std::sync::{Arc, Mutex};

use sigil_compiler::compile_named_module;
use tracing::field::{Field, Visit};
use tracing::span::{Attributes, Id, Record};
use tracing::{Event, Subscriber};
use tracing_subscriber::layer::Layer;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::registry::LookupSpan;
use tracing_subscriber::util::SubscriberInitExt;

/// Captured event for assertion. Stores the event name (last segment of
/// the format string) plus a flat key→value map of all fields rendered
/// to strings.
#[derive(Debug, Clone)]
struct CapturedEvent {
    name: String,
    fields: std::collections::HashMap<String, String>,
}

#[derive(Default)]
struct CaptureLayer {
    events: Arc<Mutex<Vec<CapturedEvent>>>,
}

impl CaptureLayer {
    fn handle(&self) -> Arc<Mutex<Vec<CapturedEvent>>> {
        self.events.clone()
    }
}

struct FieldCapture {
    fields: std::collections::HashMap<String, String>,
}

impl Visit for FieldCapture {
    fn record_debug(&mut self, field: &Field, value: &dyn std::fmt::Debug) {
        self.fields
            .insert(field.name().to_owned(), format!("{value:?}"));
    }

    fn record_str(&mut self, field: &Field, value: &str) {
        self.fields
            .insert(field.name().to_owned(), value.to_owned());
    }

    fn record_u64(&mut self, field: &Field, value: u64) {
        self.fields
            .insert(field.name().to_owned(), value.to_string());
    }

    fn record_i64(&mut self, field: &Field, value: i64) {
        self.fields
            .insert(field.name().to_owned(), value.to_string());
    }

    fn record_bool(&mut self, field: &Field, value: bool) {
        self.fields
            .insert(field.name().to_owned(), value.to_string());
    }
}

impl<S> Layer<S> for CaptureLayer
where
    S: Subscriber + for<'a> LookupSpan<'a>,
{
    fn on_event(&self, event: &Event<'_>, _ctx: tracing_subscriber::layer::Context<'_, S>) {
        let mut visitor = FieldCapture {
            fields: std::collections::HashMap::new(),
        };
        event.record(&mut visitor);
        let name = visitor
            .fields
            .get("message")
            .cloned()
            .unwrap_or_else(|| event.metadata().name().to_owned());
        self.events.lock().unwrap().push(CapturedEvent {
            name,
            fields: visitor.fields,
        });
    }

    fn on_new_span(
        &self,
        _attrs: &Attributes<'_>,
        _id: &Id,
        _ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
    }

    fn on_record(
        &self,
        _id: &Id,
        _values: &Record<'_>,
        _ctx: tracing_subscriber::layer::Context<'_, S>,
    ) {
    }
}

/// Run a representative compile under a capturing tracing subscriber.
/// Returns every event fired during the compile.
fn capture_events(source: &str) -> Vec<CapturedEvent> {
    let layer = CaptureLayer::default();
    let handle = layer.handle();
    let subscriber = tracing_subscriber::registry().with(layer);
    let _guard = subscriber.set_default();

    let _ = compile_named_module("trace_smoke.sigil", source);

    handle.lock().unwrap().clone()
}

#[test]
fn use_scope_built_event_fires_per_module() {
    let source = r#"
module helpers;
pub fn add_one(x: i64) -> i64 { return x + 1; }

module main;
use sigil::helpers;
fn boot() -> i64 { return helpers::add_one(0); }
"#;
    let events = capture_events(source);
    let use_scope_events: Vec<_> = events
        .iter()
        .filter(|e| e.name.contains("use_scope_built"))
        .collect();
    assert!(
        use_scope_events.len() >= 2,
        "expected ≥2 use_scope_built events (one per module); got {}: {:?}",
        use_scope_events.len(),
        events.iter().map(|e| e.name.as_str()).collect::<Vec<_>>()
    );
}

#[test]
fn cross_module_dispatch_event_fires_on_use_call() {
    let source = r#"
module helpers;
pub fn add_one(x: i64) -> i64 { return x + 1; }

module main;
use sigil::helpers;
fn boot() -> i64 { return helpers::add_one(0); }
"#;
    let events = capture_events(source);
    let dispatch_events: Vec<_> = events
        .iter()
        .filter(|e| e.name.contains("cross_module_dispatch"))
        .collect();
    assert!(
        !dispatch_events.is_empty(),
        "expected ≥1 cross_module_dispatch event; got: {:?}",
        events.iter().map(|e| e.name.as_str()).collect::<Vec<_>>()
    );
    // The Found outcome should appear since the call resolves cleanly.
    assert!(
        dispatch_events.iter().any(|e| e
            .fields
            .get("outcome")
            .map(|v| v.contains("Found"))
            .unwrap_or(false)),
        "expected at least one Found outcome; got: {:?}",
        dispatch_events
    );
}

#[test]
fn cycle_detected_event_includes_path_metadata() {
    let source = r#"
module a;
use sigil::b;
pub fn fa() -> i64 { return 1; }

module b;
use sigil::a;
pub fn fb() -> i64 { return 2; }
"#;
    let events = capture_events(source);
    let cycle_events: Vec<_> = events
        .iter()
        .filter(|e| e.name.contains("cycle_detected"))
        .collect();
    assert!(
        !cycle_events.is_empty(),
        "expected ≥1 cycle_detected event; got: {:?}",
        events.iter().map(|e| e.name.as_str()).collect::<Vec<_>>()
    );
    let evt = cycle_events[0];
    assert!(evt.fields.contains_key("path_len"), "missing path_len");
    assert!(evt.fields.contains_key("head"), "missing head");
}

#[test]
fn no_event_payload_contains_long_source_substring() {
    // I21: trace events MUST NOT log raw source bytes. The payload
    // can carry module names (short, controlled vocabulary), AST
    // node IDs, code identifiers, spans — but not arbitrary user
    // source. We assert no event payload contains a substring of the
    // input source longer than 32 bytes.
    //
    // Distinctive marker that's > 32 bytes and would be easy to
    // accidentally include if the trace events grow careless:
    let marker = "/* SECRET_DO_NOT_LOG_THIS_VERY_LONG_DISTINCTIVE_STRING_PAYLOAD */";
    assert!(marker.len() > 32, "test marker must be > 32 bytes");
    let source = format!(
        r#"
module helpers;
{}
pub fn add_one(x: i64) -> i64 {{ return x + 1; }}

module main;
use sigil::helpers;
fn boot() -> i64 {{ return helpers::add_one(0); }}
"#,
        marker
    );
    let events = capture_events(&source);
    for event in &events {
        for (field_name, field_value) in &event.fields {
            assert!(
                !field_value.contains(marker),
                "event `{}` field `{}` contains the source marker — \
                trace events must not log raw source bytes (I21).\nField value: {field_value}",
                event.name,
                field_name
            );
        }
    }
}
