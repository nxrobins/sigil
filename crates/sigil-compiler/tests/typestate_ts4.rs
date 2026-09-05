//! TS4 of the typestate epic — affinity-smuggle hardening (ST-6 / BL-2).
//!
//! A typestate value is affine (Linear, TS2), so the `ownership.rs` move-checker
//! catches direct use-after-transition (O001). But an aggregate is a back door: stash
//! a handle in a record field / enum payload / array, then EXTRACT IT TWICE
//! (LoadField / destructure / Index) and you have two handles from one — defeating the
//! guarantee (you can `close` the same file twice). This is the exact smuggle the
//! cap-defense (T183/T184/T186/T242) closes for capabilities; TS4 closes it for
//! typestate with **T275** by forbidding the storage outright (the boring limit).

use sigil_compiler::compile_tool;

const PROTO: &str = "\
state File { Open, Closed }\n\
record File<@S> { fd: i64 }\n\
fn open() -> File<Open> { return File { fd: 1 }; }\n\
fn shut(f: File<Open>) -> File<Closed> { return File { fd: 0 }; }\n\
fn fd<@S>(f: File<S>) -> i64 { return f.fd; }\n";

fn err_codes(src: &str) -> Vec<String> {
    match compile_tool(src) {
        Ok(_) => vec![],
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn prog(items: &str, body: &str) -> String {
    format!(
        "module tool;\n{PROTO}{items}\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}}}\n"
    )
}

// ── the smuggle is impossible: aggregate storage is rejected at the source ──────

#[test]
fn affinity_smuggle_via_record_field_is_t275() {
    // The exploit it prevents: `let b = Box { f: a }; let g1 = b.f; let g2 = b.f;
    // shut(g1); shut(g2);` — two `File<Closed>` from one `File<Open>`. Rejected at the
    // record DECLARATION, so the smuggle can never be constructed.
    let cs = err_codes(&prog("record Box { f: File<Open> }\n", "    return 0;\n"));
    assert!(
        cs.iter().any(|c| c == "T275"),
        "a typestate-typed record field must be T275; got {cs:?}"
    );
}

#[test]
fn affinity_smuggle_via_enum_payload_is_t275() {
    let cs = err_codes(&prog("enum Held { Has(File<Open>) }\n", "    return 0;\n"));
    assert!(
        cs.iter().any(|c| c == "T275"),
        "a typestate-typed enum payload must be T275; got {cs:?}"
    );
}

#[test]
fn affinity_smuggle_via_array_is_t275() {
    let cs = err_codes(&prog(
        "",
        "    let a: File<Open> = open();\n\
         \x20   let b: File<Open> = open();\n\
         \x20   let arr: [File<Open>; 2] = [a, b];\n\
         \x20   return 0;\n",
    ));
    assert!(
        cs.iter().any(|c| c == "T275"),
        "a typestate-typed array element must be T275; got {cs:?}"
    );
}

#[test]
fn typestate_nested_in_field_tuple_is_t275() {
    // The walker recurses composites: a typestate value hidden in a tuple field is
    // caught too (you can't smuggle it one layer down).
    let cs = err_codes(&prog(
        "record Box { t: (File<Open>, i64) }\n",
        "    return 0;\n",
    ));
    assert!(
        cs.iter().any(|c| c == "T275"),
        "a typestate value nested in a tuple field must be T275; got {cs:?}"
    );
}

// ── legal flows are undisturbed (no false T275) ────────────────────────────────

#[test]
fn passing_typestate_by_value_still_compiles() {
    // The sanctioned channel — pass by value through function arguments — is fine;
    // T275 only bars AGGREGATE storage, never argument passing.
    let cs = err_codes(&prog(
        "",
        "    let a: File<Open> = open();\n\
         \x20   let n: i64 = fd(a);\n\
         \x20   let b: File<Closed> = shut(open());\n\
         \x20   let m: i64 = fd(b);\n\
         \x20   return n + m;\n",
    ));
    assert!(
        cs.is_empty(),
        "passing typestate by value must compile (no false T275); got {cs:?}"
    );
}

// ── adversarial-sweep finds: the smuggle has non-aggregate channels too ────────

#[test]
fn typestate_in_actor_state_is_t275() {
    // The actor-side aggregate: an actor can take a typestate value out of its state
    // across handler calls more than once. Caps ARE allowed in actor state (the
    // sanctioned holding place); typestate is not.
    //
    // No `tool_main` here: this is an actor-world program (M011 forbids an actor in a
    // tool project). The `state`/`record`/`actor` alone reach the type-checker, which
    // rejects the typestate-in-actor-state field with T275 before any entry is needed.
    let cs = err_codes(
        "module tool;\n\
         state File { Open, Closed }\n\
         record File<@S> { fd: i64 }\n\
         fn open() -> File<Open> { return File { fd: 1 }; }\n\
         actor Stash {\n\
         \x20   state { f: File<Open> }\n\
         \x20   init(x: File<Open>) {}\n\
         \x20   on Noop() -> i64 { return 0; }\n\
         }\n",
    );
    assert!(
        cs.iter().any(|c| c == "T275"),
        "a typestate actor-state field must be T275; got {cs:?}"
    );
}

#[test]
fn closure_capturing_typestate_cannot_be_reused() {
    // A closure capturing an affine typestate value is itself LINEAR (lambda-lift
    // copies the captured handle into the heap `__env` — a second handle), so it
    // cannot bind to a non-linear `Fn` type and be called twice. Closes the
    // closure-capture double-consume vector (a closure here could `shut(a)` on every
    // call → many `File<Closed>` from one `File<Open>`).
    let cs = err_codes(&prog(
        "",
        "    let a: File<Open> = open();\n\
         \x20   let c: Fn() -> i64 = fn() -> i64 { let r: File<Closed> = shut(a); return r.fd; };\n\
         \x20   let x: i64 = c();\n\
         \x20   let y: i64 = c();\n\
         \x20   return x + y;\n",
    ));
    assert!(
        !cs.is_empty(),
        "a typestate-capturing closure must be rejected; got {cs:?}"
    );
}

#[test]
fn typestate_as_closure_param_compiles() {
    // The sanctioned channel (like caps): pass the typestate value as a closure
    // PARAMETER, not a capture — no copy, single-use, fine.
    let cs = err_codes(&prog(
        "",
        "    let g: Fn(File<Open>) -> i64 = fn(f: File<Open>) -> i64 { let r: File<Closed> = shut(f); return r.fd; };\n\
         \x20   let a: File<Open> = open();\n\
         \x20   let n: i64 = g(a);\n\
         \x20   return n;\n",
    ));
    assert!(
        cs.is_empty(),
        "passing typestate as a closure parameter must compile; got {cs:?}"
    );
}

#[test]
fn non_typestate_aggregates_unaffected() {
    // A record of ordinary fields is untouched — the gate is precise to typestate.
    let cs = err_codes(&prog(
        "record Plain { n: i64, b: bool }\n",
        "    let p: Plain = Plain { n: 5, b: true };\n\
         \x20   return p.n;\n",
    ));
    assert!(
        cs.is_empty(),
        "an ordinary record must be unaffected by the typestate gate; got {cs:?}"
    );
}
