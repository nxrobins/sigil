//! Mutable actor-state marker syntax.
//!
//! An optional leading `mut` on an actor `state {}` field is captured in the shared
//! `Field.mutability` and permits the bounded handler-write surface.
//!
//! These pin: (1) `mut` on a state field is captured as `Mutability::Mut` (a plain field stays
//! `Default`); (2) `mut` on a RECORD field is REJECTED (P030) — the shared field grammar must
//! not leak the state-only keyword into records; (3) a handler write to a marked field is allowed.

use sigil_compiler::ast::{Item, Mutability};
use sigil_compiler::compile_named_module;
use sigil_compiler::parser;
use sigil_compiler::source::SourceFile;

// ── (1) `mut` on a state field is captured as Mutability::Mut ──────────────────────────────
#[test]
fn mut_state_field_is_captured_as_mut() {
    let src = r#"module sigil;
actor Worker {
    state { mut n: i64, tag: i64 }
    init() { n = 0; tag = 1; }
    on Get() -> i64 { return n + tag; }
}
"#;
    let source = SourceFile::new("mut_state.sigil", src);
    let (program, diags) = parser::parse(&source);
    assert!(
        !diags
            .iter()
            .any(|d| d.severity() == sigil_compiler::Severity::Error),
        "a `mut` state field must parse cleanly; got {diags:?}"
    );
    let actor = program
        .modules
        .iter()
        .flat_map(|m| &m.items)
        .find_map(|item| match item {
            Item::ActorDef(def) if def.name == "Worker" => Some(def),
            _ => None,
        })
        .expect("Worker actor present");
    let n = actor
        .state_fields
        .iter()
        .find(|f| f.name == "n")
        .expect("state field n");
    let tag = actor
        .state_fields
        .iter()
        .find(|f| f.name == "tag")
        .expect("state field tag");
    assert_eq!(
        n.mutability,
        Mutability::Mut,
        "`mut n` must be captured as Mutability::Mut, not silently dropped"
    );
    assert_eq!(
        tag.mutability,
        Mutability::Default,
        "a bare state field stays Mutability::Default"
    );
}

// ── (2) `mut` on a record field is rejected (P030) — the state-only keyword must not leak ──
#[test]
fn mut_on_a_record_field_is_rejected() {
    let src = r#"module sigil;
record R { mut x: i64 }
"#;
    let source = SourceFile::new("mut_record.sigil", src);
    let (_program, diags) = parser::parse(&source);
    assert!(
        diags.iter().any(|d| d.code().as_str() == "P030"),
        "`mut` on a record field must be rejected with P030; got {diags:?}"
    );
}

// ── (3) a handler write to a `mut` state field is permitted from S2 onward ──────────────────
#[test]
fn mut_state_field_handler_write_is_permitted() {
    // A handler write to a `mut` field compiles. A non-`mut` field still fails T123; see
    // state_mut_fences.rs.
    let src = r#"module sigil;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { let w = spawn::<Worker>(fuel); return 0; }
}
actor Worker {
    state { mut n: i64 }
    init(f: Fuel) { n = 0; }
    on Set(v: i64) { n = v; }
}
"#;
    compile_named_module("mut_state_write.sigil", src)
        .expect("from S2, a handler write to a `mut` state field is permitted (T123 relaxed)");
}
