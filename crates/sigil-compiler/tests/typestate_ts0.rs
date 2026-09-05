//! TS0 of the typestate (lightweight dependent types) epic — representation +
//! parse + resolve foundation (no-op).
//!
//! A protocol state is a phantom type argument on a nominal: `File<Open>` is
//! `Type::Named("File", [Type::StateMarker("Open")])`, declared via a `state Name
//! { … }` item and a `@S` state-kinded binder on the carrier record. TS0 adds the
//! representation, parsing, and resolution; it ERASES before AIR (state-blind
//! `mangle_type`), so a program using stated types lowers BYTE-IDENTICALLY to its
//! `<@S>`-stripped twin (the no-op gate, ST-1). The closed state set is enforced at
//! resolution (ST-5 → T276); a malformed `@S` binder is P028.
//!
//! See docs/specs/typestate-in-sigil.md.

use sigil_compiler::ast::{Item, ParamKind};
use sigil_compiler::compile_tool;
use sigil_test_utils::parse_program;

// A `tool_main` shell so `compile_tool` has its required entry point.
const MAIN: &str =
    "pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } { return 0 - 1; }\n";

fn codes_of_err(src: &str) -> Vec<String> {
    let err = compile_tool(src).expect_err("expected the program to be rejected");
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect()
}

// ── parse: AST shape ───────────────────────────────────────────────────────────

#[test]
fn state_decl_parses_to_closed_marker_set() {
    let prog = parse_program!("module m;\nstate File { Open, Closed }\n");
    let Item::StateDef(def) = &prog.modules[0].items[0] else {
        panic!("expected the first item to be a StateDef");
    };
    assert_eq!(def.name, "File");
    assert_eq!(def.states, vec!["Open".to_string(), "Closed".to_string()]);
}

#[test]
fn state_kinded_binder_parses() {
    // `record File<@S>` → a single STATE-kinded type parameter named `S`.
    let prog = parse_program!("module m;\nrecord File<@S> { fd: i64 }\n");
    let Item::RecordDef(def) = &prog.modules[0].items[0] else {
        panic!("expected a RecordDef");
    };
    assert_eq!(def.type_params.len(), 1);
    assert_eq!(def.type_params[0].name, "S");
    assert_eq!(def.type_params[0].kind, ParamKind::State);
    assert!(def.type_params[0].bounds.is_empty());
}

#[test]
fn state_binder_coexists_with_ordinary_and_hkt_params() {
    // `<T, @S>` — an ordinary `Star` param and a `State` param side by side.
    let prog = parse_program!("module m;\nrecord Buf<T, @S> { v: T }\n");
    let Item::RecordDef(def) = &prog.modules[0].items[0] else {
        panic!("expected a RecordDef");
    };
    assert_eq!(def.type_params[0].kind, ParamKind::Star);
    assert_eq!(def.type_params[1].kind, ParamKind::State);
}

// ── resolve + type-check: declared-and-used compiles ───────────────────────────

#[test]
fn declared_typestate_compiles() {
    // TS0 done-line: declaring a protocol + carrier record and USING `File<Open>`
    // in a function signature/body parses, resolves, and type-checks. (No value is
    // constructed — the mint is TS1.)
    let src = format!(
        "module tool;\n\
         state File {{ Open, Closed }}\n\
         record File<@S> {{ fd: i64 }}\n\
         pub fn read_fd(f: File<Open>) -> i64 {{ return f.fd; }}\n\
         {MAIN}"
    );
    assert!(
        compile_tool(&src).is_ok(),
        "a program declaring + using a stated type must compile: {:?}",
        compile_tool(&src).err().map(|e| e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect::<Vec<_>>())
    );
}

// ── ST-5: the state set is closed ──────────────────────────────────────────────

#[test]
fn undeclared_state_marker_rejected_t276() {
    // `File<Banana>` when `state File { Open, Closed }` — Banana ∉ the closed set.
    let src = format!(
        "module tool;\n\
         state File {{ Open, Closed }}\n\
         record File<@S> {{ fd: i64 }}\n\
         pub fn read_fd(f: File<Banana>) -> i64 {{ return f.fd; }}\n\
         {MAIN}"
    );
    assert!(
        codes_of_err(&src).iter().any(|c| c == "T276"),
        "an undeclared state marker must be T276; got {:?}",
        codes_of_err(&src)
    );
}

// ── P028: a state binder takes no `:` bound/kind annotation ─────────────────────

#[test]
fn state_binder_with_bound_rejected_p028() {
    let src = format!(
        "module tool;\n\
         record File<@S: Hash> {{ fd: i64 }}\n\
         {MAIN}"
    );
    assert!(
        codes_of_err(&src).iter().any(|c| c == "P028"),
        "a `@S: Bound` binder must be P028; got {:?}",
        codes_of_err(&src)
    );
}

// ── ST-1: erases byte-identically to the `<@S>`-stripped twin ───────────────────

#[test]
fn erases_to_byte_identical_stripped_twin() {
    // The STATED program: a protocol + carrier record + a function that takes a
    // `File<Open>` and reads its field (the field-access path exercises the
    // state-blind `mangle_type` / field-registry key).
    let stated = format!(
        "module tool;\n\
         state File {{ Open, Closed }}\n\
         record File<@S> {{ fd: i64 }}\n\
         pub fn read_fd(f: File<Open>) -> i64 {{ return f.fd; }}\n\
         {MAIN}"
    );
    // The TWIN: the SAME program with every `<@S>` / `<Open>` textually removed and
    // the `state` decl dropped — an ordinary non-stated `File` record.
    let twin = format!(
        "module tool;\n\
         record File {{ fd: i64 }}\n\
         pub fn read_fd(f: File) -> i64 {{ return f.fd; }}\n\
         {MAIN}"
    );

    let stated_wasm = compile_tool(&stated)
        .expect("stated program must compile")
        .wasm;
    let twin_wasm = compile_tool(&twin).expect("twin program must compile").wasm;

    assert!(!stated_wasm.is_empty(), "stated wasm must be non-empty");
    assert_eq!(
        stated_wasm,
        twin_wasm,
        "typestate must erase before AIR: the stated program's wasm ({} bytes) must be \
         byte-identical to its `<@S>`-stripped twin ({} bytes)",
        stated_wasm.len(),
        twin_wasm.len()
    );
}
