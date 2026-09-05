//! Effect Handlers — the algebraic-effects epic (operations + abortive +
//! scoped-resume). See `docs/specs/effect-handlers-in-sigil.md`.
//!
//! EH0 (this rung) pins the PARSE + AST surface and the intermediate-rung gate:
//!   - `effect Name { fn op(..) -> Ty; }` parses (operations grow the bare marker).
//!   - `perform Effect.op(args)`, clause-form `handle e { Op(x) => .. }`, and
//!     `resume e` parse, but are rejected at type-check with **E004** until the
//!     later rungs implement them — so they never reach AIR (byte-identical AIR).
//!   - the legacy bare `handle E { .. }` row-widening form is UNAFFECTED
//!     (C-PATHSEP): it must not be mis-routed to the clause path.

use sigil_compiler::compile_named_module;

/// Compile `src` as a module; return the sorted, de-duplicated emitted codes
/// (empty = compiled cleanly).
fn codes(src: &str) -> Vec<String> {
    match compile_named_module("effect_handlers.sigil", src.to_string()) {
        Ok(_) => Vec::new(),
        Err(e) => {
            let mut cs: Vec<String> = e
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_owned())
                .collect();
            cs.sort();
            cs.dedup();
            cs
        }
    }
}

fn assert_has(src: &str, code: &str) {
    let cs = codes(src);
    assert!(
        cs.iter().any(|c| c == code),
        "expected {code} for source:\n{src}\ngot {cs:?}"
    );
}

fn assert_lacks(src: &str, code: &str) {
    let cs = codes(src);
    assert!(
        !cs.iter().any(|c| c == code),
        "did NOT expect {code} for source:\n{src}\ngot {cs:?}"
    );
}

// ── Operations parse (the bare marker grew typed operations) ─────────────────

#[test]
fn effect_with_operations_parses() {
    // A `fn op(..) -> Ty;` signature inside the effect body must parse with no
    // parser error (P-codes). The effect is otherwise unused.
    let src = "module sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        effect Fail { fn raise(msg: str) -> never; }\n";
    let cs = codes(src);
    assert!(
        !cs.iter().any(|c| c.starts_with('P')),
        "effect operations should parse without P-codes, got {cs:?}"
    );
}

#[test]
fn bare_marker_effect_still_parses() {
    // The legacy bare `effect Name;` form is unchanged.
    let src = "module sigil;\n\
        effect Audit;\n";
    let cs = codes(src);
    assert!(
        !cs.iter().any(|c| c.starts_with('P')),
        "bare marker effect should parse, got {cs:?}"
    );
}

// ── The new surface parses but is gated by E004 ─────────────────────────────

#[test]
fn perform_is_gated_by_e004() {
    let src = "module sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn f() -> i64 { return perform Reader.get(); }\n";
    assert_has(src, "E004");
}

#[test]
fn clause_handle_is_gated_by_e004() {
    let src = "module sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn provider() -> i64 { return 1; }\n\
        fn f() -> i64 { return handle provider() { Reader.get() => 7 }; }\n";
    assert_has(src, "E004");
}

#[test]
fn resume_in_clause_is_gated_by_e004() {
    let src = "module sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn provider() -> i64 { return 1; }\n\
        fn f() -> i64 { return handle provider() { Reader.get() => resume 42 }; }\n";
    assert_has(src, "E004");
}

// ── C-PATHSEP: the bare row-widening `handle` is NOT mis-routed to clauses ────

#[test]
fn bare_handle_block_is_not_e004() {
    // `handle Audit { <stmt> }` is the legacy bare form (no clauses, no `=>`):
    // it must take the existing inline path, NOT the new clause path, so E004
    // must NOT fire.
    let src = "module sigil;\n\
        effect Audit;\n\
        fn f() -> i64 { handle Audit { let x = 1; } return 2; }\n";
    assert_lacks(src, "E004");
}

#[test]
fn perform_is_a_plain_identifier_outside_the_trigger_shape() {
    // `perform` is contextual: as an ordinary variable name it must still work
    // (the trigger is only `perform <Ident> .`). No E004, no P-codes.
    let src = "module sigil;\n\
        fn f() -> i64 { let perform = 3; return perform; }\n";
    let cs = codes(src);
    assert!(
        !cs.iter().any(|c| c == "E004" || c.starts_with('P')),
        "`perform` as an identifier should be unaffected, got {cs:?}"
    );
}

#[test]
fn resume_is_a_plain_identifier_outside_a_clause() {
    // `resume` is only special inside a clause body; elsewhere it is an ordinary
    // identifier.
    let src = "module sigil;\n\
        fn f() -> i64 { let resume = 5; return resume; }\n";
    let cs = codes(src);
    assert!(
        !cs.iter().any(|c| c == "E004" || c.starts_with('P')),
        "`resume` as an identifier should be unaffected, got {cs:?}"
    );
}

// ── EH1: perform shape-checking (E005 unknown op / E006 unknown effect / E007) ─

#[test]
fn perform_unknown_operation_is_e005() {
    // `Reader` is declared with op `get`, but `missing` is not an operation.
    let src = "module sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn f() -> i64 { return perform Reader.missing(); }\n";
    assert_has(src, "E005");
    assert_lacks(src, "E004"); // a real error, not the not-yet gate
}

#[test]
fn perform_unknown_effect_is_e006() {
    // `Nope` is not a declared effect at all.
    let src = "module sigil;\n\
        fn f() -> i64 { return perform Nope.get(); }\n";
    assert_has(src, "E006");
    assert_lacks(src, "E004");
}

#[test]
fn perform_wrong_arg_count_is_e007() {
    // `get` takes 0 args; passing one is an arity error.
    let src = "module sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn f() -> i64 { return perform Reader.get(1); }\n";
    assert_has(src, "E007");
    assert_lacks(src, "E004");
}

#[test]
fn well_formed_perform_is_e004_not_a_shape_error() {
    // A perform whose effect+op resolve and whose arity matches is WELL-FORMED;
    // it is still gated by E004 (lowering not implemented), but must NOT emit any
    // of the shape-error codes.
    let src = "module sigil;\n\
        effect Calc { fn add(a: i64, b: i64) -> i64; }\n\
        fn f() -> i64 { return perform Calc.add(2, 3); }\n";
    let cs = codes(src);
    assert!(
        cs.iter().any(|c| c == "E004"),
        "expected E004 gate, got {cs:?}"
    );
    for bad in ["E005", "E006", "E007"] {
        assert!(
            !cs.iter().any(|c| c == bad),
            "well-formed perform should not emit {bad}, got {cs:?}"
        );
    }
}

// ── EH2: clause-handle checking (coverage E008 / bare-on-op-effect E009) ──────

const CALC: &str = "module sigil;\n\
    effect Calc { fn add(a: i64, b: i64) -> i64; fn sub(a: i64, b: i64) -> i64; }\n\
    effect One { fn op() -> i64; }\n\
    effect Reader { fn get() -> i64; }\n\
    fn provider() -> i64 { return 1; }\n";

#[test]
fn clause_handle_missing_coverage_is_e008() {
    // `Calc` has add + sub; covering only `add` leaves `sub` uncovered.
    let src =
        format!("{CALC}fn f() -> i64 {{ return handle provider() {{ Calc.add(a, b) => 0 }}; }}\n");
    assert_has(&src, "E008");
}

#[test]
fn clause_handle_full_coverage_is_e004_not_e008() {
    // Covering every operation of `Calc` is well-formed — gated by E004, no E008.
    let src = format!(
        "{CALC}fn f() -> i64 {{ return handle provider() {{ Calc.add(a, b) => 0, Calc.sub(a, b) => 1 }}; }}\n"
    );
    let cs = codes(&src);
    assert!(
        cs.iter().any(|c| c == "E004"),
        "expected E004 gate, got {cs:?}"
    );
    assert!(
        !cs.iter().any(|c| c == "E008"),
        "full coverage should not emit E008, got {cs:?}"
    );
}

#[test]
fn clause_handle_duplicate_clause_is_e008() {
    // `One` has one op; two clauses for it is a duplicate.
    let src = format!(
        "{CALC}fn f() -> i64 {{ return handle provider() {{ One.op() => 0, One.op() => 1 }}; }}\n"
    );
    assert_has(&src, "E008");
}

#[test]
fn clause_handle_unknown_operation_is_e005() {
    let src = format!(
        "{CALC}fn f() -> i64 {{ return handle provider() {{ Reader.missing() => 0 }}; }}\n"
    );
    assert_has(&src, "E005");
}

#[test]
fn clause_handle_wrong_binder_count_is_e007() {
    // `Calc.add` has two parameters; binding none is an arity mismatch.
    let src = format!(
        "{CALC}fn f() -> i64 {{ return handle provider() {{ Calc.add() => 0, Calc.sub(a, b) => 1 }}; }}\n"
    );
    assert_has(&src, "E007");
}

#[test]
fn bare_handle_on_operation_effect_is_e009() {
    // A bare `handle Reader { .. }` (Reader declares `get`) needs the clause form.
    let src = format!("{CALC}fn f() -> i64 {{ handle Reader {{ let x = 1; }}; return 2; }}\n");
    assert_has(&src, "E009");
}

#[test]
fn bare_handle_on_marker_effect_is_clean() {
    // A bare `handle` of a MARKER effect (no operations) is unaffected — no E009.
    let src = "module sigil;\n\
        effect Audit;\n\
        fn f() -> i64 { handle Audit { let x = 1; }; return 2; }\n";
    assert_lacks(src, "E009");
}

// ── EH3.1: Type::Never + operation type resolution ───────────────────────────

#[test]
fn abortive_operation_with_never_return_resolves() {
    // `fn raise(..) -> never` registers cleanly (the return resolves to the
    // abortive bottom `Type::Never`) — no spurious diagnostics on the decl.
    let src = "module sigil;\n\
        effect Fail { fn raise(msg: str) -> never; }\n";
    let cs = codes(src);
    assert!(
        cs.is_empty(),
        "abortive op decl should be clean, got {cs:?}"
    );
}

#[test]
fn perform_of_abortive_operation_is_well_formed() {
    // A `perform` of an abortive (`-> never`) operation with matching arity is
    // well-formed — gated by E004, not a shape error.
    let src = "module sigil;\n\
        effect Fail { fn raise(msg: str) -> never; }\n\
        fn f() { perform Fail.raise(\"boom\"); }\n";
    let cs = codes(src);
    assert!(
        cs.iter().any(|c| c == "E004"),
        "expected E004 gate, got {cs:?}"
    );
    for bad in ["E005", "E006", "E007"] {
        assert!(
            !cs.iter().any(|c| c == bad),
            "abortive perform should not emit {bad}, got {cs:?}"
        );
    }
}

// ── EH3.2: typed nodes flow through the security passes (C-VIS) ───────────────

#[test]
fn cvis_effect_leak_in_clause_body_is_flagged() {
    // C-VIS: a security pass (effect_check) must DESCEND into a clause body, not
    // merely have the gate fire. An effect leak (`Log` is not in the outer-ring
    // function's row) inside a clause body is flagged E001. effect_check runs
    // BEFORE the E004 gate, so E001 halts compilation first — proving the walker
    // traverses the new node's sub-trees.
    let src = "#[ring(outer)]\nmodule sigil;\n\
        effect Log;\n\
        effect Reader { fn get() -> i64; }\n\
        fn logs() -> i64 ! { Log } { return 0; }\n\
        fn provider() -> i64 { return 1; }\n\
        fn f() -> i64 { return handle provider() { Reader.get() => logs() }; }\n";
    assert_has(src, "E001");
}

#[test]
fn cvis_effect_leak_in_perform_arg_is_flagged() {
    // C-VIS: effect_check descends into a `perform`'s arguments.
    let src = "#[ring(outer)]\nmodule sigil;\n\
        effect Log;\n\
        effect Sink { fn put(x: i64); }\n\
        fn logs() -> i64 ! { Log } { return 0; }\n\
        fn f() -> i64 { perform Sink.put(logs()); return 0; }\n";
    assert_has(src, "E001");
}

// ── EH3.3: effect discharge + orphan-perform (E010) ──────────────────────────

#[test]
fn orphan_perform_undeclared_effect_is_e010() {
    // Outer-ring `f` performs `Reader.get` but does not declare `Reader`.
    let src = "#[ring(outer)]\nmodule sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn f() -> i64 { return perform Reader.get(); }\n";
    assert_has(src, "E010");
}

#[test]
fn declared_perform_is_not_orphan() {
    // Declaring the effect in the row clears the orphan check; the well-formed
    // perform is then E004-gated (not E010).
    let src = "#[ring(outer)]\nmodule sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn f() -> i64 ! { Reader } { return perform Reader.get(); }\n";
    let cs = codes(src);
    assert!(
        cs.iter().any(|c| c == "E004"),
        "expected E004 gate, got {cs:?}"
    );
    assert!(
        !cs.iter().any(|c| c == "E010"),
        "a declared perform is not orphan, got {cs:?}"
    );
}

#[test]
fn handle_discharges_scrutinee_effect_no_e001() {
    // `producer` declares `! { Reader }`. Calling it bare in a Reader-less outer
    // function LEAKS (E001); wrapping it in a clause-handle that covers Reader
    // DISCHARGES the effect — no E001 (only the E004 gate).
    let leak = "#[ring(outer)]\nmodule sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn producer() -> i64 ! { Reader } { return 0; }\n\
        fn f() -> i64 { return producer(); }\n";
    assert_has(leak, "E001");

    let discharged = "#[ring(outer)]\nmodule sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn producer() -> i64 ! { Reader } { return 0; }\n\
        fn f() -> i64 { return handle producer() { Reader.get() => 0 }; }\n";
    let cs = codes(discharged);
    assert!(
        !cs.iter().any(|c| c == "E001"),
        "handle should discharge Reader (no E001), got {cs:?}"
    );
    assert!(
        cs.iter().any(|c| c == "E004"),
        "expected E004 gate, got {cs:?}"
    );
}

// ── EH4.0 adversarial-sweep regressions: holes now gate/reject, never miscompile ─

#[test]
fn eh40_resume_capturing_handle_var_gates() {
    // EH4-H4: the resumed expression references a handle-scope variable (`s`), not
    // a clause binder. The whitelist gates it (E004) — a naive capture walk could
    // miss by-name channels and synthesize an unsound capture-free closure.
    let src = "#[ring(outer)]\nmodule sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn f() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        fn run() -> i64 { let s = 7; return handle f() { Reader.get() => resume s }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh40_resume_calling_a_function_gates() {
    // EH4-H4: the resumed expression is a call — outside the simple whitelist, so
    // it stays gated rather than being inlined into a synthesized closure.
    let src = "#[ring(outer)]\nmodule sigil;\n\
        effect Reader { fn get() -> i64; }\n\
        fn helper() -> i64 { return 9; }\n\
        fn f() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        fn run() -> i64 { return handle f() { Reader.get() => resume helper() }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh43d_multi_module_program_compiles() {
    // EH4.3d: a multi-module program whose effect-handler part is confined to one
    // (outer-ring) module now compiles — the threading analysis is program-wide and
    // the unrelated module `b` is untouched. (Was conservatively E004-gated through
    // EH4.3c.) Cross-module runtime coverage: `eh43d_cross_module_*` in the runtime suite.
    let src = "#[ring(outer)]\nmodule a;\n\
        effect Reader { fn get() -> i64; }\n\
        fn f() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        fn run() -> i64 { return handle f() { Reader.get() => resume 42 }; }\n\
        module b;\n\
        fn other() -> i64 { return 1; }\n";
    assert!(
        codes(src).is_empty(),
        "single-module-effect-handler in a multi-module program should compile: got {:?}",
        codes(src)
    );
}

#[test]
fn eh43d_cross_ring_handler_rejected() {
    // EH4.3d LC-MM-RING: a handler (in inner-ring `tool`) wrapping a performer (in
    // outer-ring `lib`) would synthesize the clause closure in the inner ring and have
    // the outer-ring performer `IndirectCall` it through the wrong per-ring wasm table.
    // Cross-ring is rejected (here R004 — the ring check catches the cross-ring call —
    // with the desugar's own LC-MM-RING gate as defense-in-depth), never invalid wasm.
    let src = "#[ring(outer)]\nmodule lib;\n\
        effect Reader { fn get() -> i64; }\n\
        pub fn perf() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        module tool;\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle lib::perf() { Reader.get() => resume 42 }; return 0 - r; }\n";
    assert!(
        !codes(src).is_empty(),
        "cross-ring handler must be rejected, not miscompiled"
    );
}

#[test]
fn eh40_wrong_effect_clause_does_not_miscompile() {
    // EH4-H1: `provider` performs `E1.dat` but the handle's clause is for `E2.dat`.
    // The program MUST be rejected (here `E001` — `E1` is left undischarged), never
    // silently run the `E2` clause as `E1`'s handler. (The desugar additionally
    // requires the clause op to equal the performed op as defense-in-depth.)
    let src = "#[ring(outer)]\nmodule sigil;\n\
        effect E1 { fn dat() -> i64; }\n\
        effect E2 { fn dat() -> i64; }\n\
        fn provider() -> i64 ! { E1 } { return perform E1.dat(); }\n\
        fn run() -> i64 { return handle provider() { E2.dat() => resume 77 }; }\n";
    let cs = codes(src);
    assert!(
        !cs.is_empty(),
        "wrong-effect handler must be rejected, not miscompiled"
    );
}

// ── EH4.1: multi-operation effects (one evidence closure per operation) ────────

#[test]
fn eh41_multi_op_handler_compiles() {
    // A two-operation effect whose performer performs BOTH operations and whose
    // handler covers both: the desugar threads one evidence closure per operation,
    // so the program lowers cleanly (no E004 gate).
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect State { fn get() -> i64; fn put(v: i64) -> i64; }\n\
        fn worker() -> i64 ! { State } { let a = perform State.get(); let b = perform State.put(a + 1); return a + b; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { return handle worker() { State.get() => resume 10, State.put(x) => resume x * 2 }; }\n";
    assert!(
        codes(src).is_empty(),
        "multi-op handler should compile: got {:?}",
        codes(src)
    );
}

#[test]
fn eh41_resume_type_mismatch_gates() {
    // A clause whose resumed value is not assignable to the operation's return type
    // (`bool` resumed for an `-> i64` operation) MUST gate (E004) rather than
    // synthesize an ill-typed closure body — the resume-type-match guard.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect E { fn get() -> i64; }\n\
        fn f() -> i64 ! { E } { return perform E.get(); }\n\
        fn run() -> i64 { return handle f() { E.get() => resume true }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh41_subset_performer_compiles() {
    // The handler covers all of `State`'s operations (required by E008), but the
    // performer performs only `get`. EH4.3's per-effect threading gives `worker`
    // evidence for ALL of `State`'s operations (from the effect declaration, not the
    // perform sites), so the unused `put` evidence is simply never called — this is
    // sound and compiles (EH4.0–4.2 conservatively gated it; the threading model
    // handles it). Runtime coverage: `eh43_subset_performer_runs`.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect State { fn get() -> i64; fn put(v: i64) -> i64; }\n\
        fn worker() -> i64 ! { State } { return perform State.get(); }\n\
        fn run() -> i64 { return handle worker() { State.get() => resume 10, State.put(x) => resume x * 2 }; }\n";
    assert!(
        codes(src).is_empty(),
        "subset-performer should compile under EH4.3 threading: got {:?}",
        codes(src)
    );
}

// ── EH4.1 adversarial-sweep root fix: perform args are type-checked vs the op's
//    declared parameter types (T071). Without this, the desugar read the op
//    signature off the (unchecked) perform site and built a mistyped evidence
//    closure → invalid wasm / ICE / a SILENT miscompile. ───────────────────────

#[test]
fn perform_bool_arg_for_int_op_rejects() {
    // Was: clean compile → non-validating wasm. Now: T071 at type-check.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect S { fn put(p: i64) -> i64; }\n\
        fn worker() -> i64 ! { S } { return perform S.put(true); }\n\
        fn run() -> i64 { return handle worker() { S.put(x) => resume x }; }\n";
    assert_has(src, "T071");
}

#[test]
fn perform_u64_arg_for_int_op_rejects() {
    // The critical SILENT-miscompile case: a `u64` arg made the synthesized closure
    // binder `u64`, selecting unsigned division (`I64DivU`) for an `i64`-typed
    // handler body — valid wasm, wrong value. Now rejected (T071).
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect E { fn op(p: i64) -> i64; }\n\
        fn worker() -> i64 ! { E } { let z: u64 = 0 - 1; return perform E.op(z); }\n\
        fn run() -> i64 { return handle worker() { E.op(b) => resume b / 2 }; }\n";
    assert_has(src, "T071");
}

#[test]
fn perform_str_arg_for_int_op_rejects() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect E { fn op(p: i64) -> i64; }\n\
        fn worker(s: str) -> i64 ! { E } { return perform E.op(s); }\n\
        fn run() -> i64 { return handle worker(\"x\") { E.op(b) => resume b + 1 }; }\n";
    assert_has(src, "T071");
}

#[test]
fn perform_record_arg_for_int_op_rejects() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        record R { x: i64 }\n\
        effect E { fn op(p: i64) -> i64; }\n\
        fn worker(r: R) -> i64 ! { E } { return perform E.op(r); }\n\
        fn run() -> i64 { return handle worker(R { x: 1 }) { E.op(b) => resume 9 }; }\n";
    assert_has(src, "T071");
}

#[test]
fn perform_int_literal_for_narrow_op_param_compiles() {
    // No over-rejection: the arg-type check runs during inference, so an integer
    // LITERAL is still range-checked against the declared param (here `i32`) rather
    // than pre-defaulted to i64 and rejected. `99` fits `i32`, so this compiles.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect E { fn op(p: i32) -> i64; }\n\
        fn worker() -> i64 ! { E } { return perform E.op(99); }\n\
        fn run() -> i64 { return handle worker() { E.op(b) => resume 5 }; }\n";
    assert_lacks(src, "T071");
    assert!(
        codes(src).is_empty(),
        "should compile cleanly: got {:?}",
        codes(src)
    );
}

// ── EH4.2: abortive clauses (no resume; op return = never → early return) ──────

#[test]
fn eh42_abortive_handler_compiles() {
    // An abortive operation (`raise -> never`) with a no-resume clause whose value
    // matches the performer's return type lowers cleanly (no E004 gate).
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn parse(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x * 2; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { return handle parse(5) { Fail.raise(m) => 99 }; }\n";
    assert!(
        codes(src).is_empty(),
        "abortive handler should compile: got {:?}",
        codes(src)
    );
}

#[test]
fn eh42_abort_type_mismatch_gates() {
    // LC-ABORT-TY: the abortive clause's value (`str`) must match the performer's
    // return type (`i64`); the synthesized closure declares `i64`, so a `str` body
    // would be ill-typed. Gate (E004) rather than emit invalid wasm.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn parse(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x * 2; }\n\
        fn run() -> i64 { return handle parse(5) { Fail.raise(m) => \"oops\" }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh42_resume_clause_on_abortive_op_gates() {
    // Shape-match: a `resume` clause on an abortive (`-> never`) operation is a
    // mismatch (you cannot resume past `never`) → gated.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn parse(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x * 2; }\n\
        fn run() -> i64 { return handle parse(5) { Fail.raise(m) => resume 5 }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh42_value_clause_on_scoped_op_gates() {
    // Shape-match: a no-resume (abortive-shaped) clause on a SCOPED operation is a
    // mismatch → gated (the scoped perform expects a resumed value).
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect R { fn get() -> i64; }\n\
        fn f() -> i64 ! { R } { return perform R.get(); }\n\
        fn run() -> i64 { return handle f() { R.get() => 5 }; }\n";
    assert_has(src, "E004");
}

// ── EH4.3c: abortive propagation via the EhResult discriminated-union return ───

#[test]
fn eh43c_abortive_tail_propagation_compiles() {
    // An ABORTIVE op performed in an INTERMEDIATE callee (`helper`), reached by a
    // TAIL call (`return helper(x)`). EH4.3c lowers this via a synthesized
    // `$EhResult$<H>` enum: `helper` aborts → `return Aborted(ev(args))`, `g`
    // propagates by returning `helper`'s `EhResult` directly, and the handle
    // `$eh_unwrap`s the result. Compiles (was E004-gated through EH4.3b). Runtime
    // coverage: `eh43c_tail_propagation_runs`.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn helper(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x; }\n\
        fn g(x: i64) -> i64 ! { Fail } { return helper(x); }\n\
        fn run() -> i64 { return handle g(0 - 1) { Fail.raise(m) => 99 }; }\n";
    assert!(
        codes(src).is_empty(),
        "tail-call abortive propagation should compile: got {:?}",
        codes(src)
    );
}

#[test]
fn eh43c_non_tail_abortive_propagation_gates() {
    // A NON-tail abortive-effect call (`let a = helper(x); …`) is still gated (E004):
    // EH4.3c only propagates in TAIL position (a non-tail propagation would need a
    // dummy-init `let mut` / continuation split — out of scope; LC-EHR-TAIL).
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn helper(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x; }\n\
        fn g(x: i64) -> i64 ! { Fail } { let a = helper(x); return a + 1; }\n\
        fn run() -> i64 { return handle g(0 - 1) { Fail.raise(m) => 99 }; }\n";
    assert_has(src, "E004");
}

// ── EH4.3a/b sweep fixes: entry must not be threaded; no abortive forwarding ───

#[test]
fn eh43_entry_with_effect_row_gates() {
    // `tool_main` is the entry: its exported ABI is a contract and must never receive
    // evidence params. The mangled name is `tool::tool_main`, so a bare-string entry
    // check missed it and threaded the entry (corrupting the ABI → runaway recursion
    // when it performs). Now gated (E004).
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect E { fn op() -> i64; }\n\
        fn leaf() -> i64 ! { E } { return perform E.op(); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 ! { E } { let r = handle leaf() { E.op() => resume 5 }; let x = perform E.op(); return 0 - (r + x); }\n";
    assert_has(src, "E004");
}

#[test]
fn eh43_abortive_forwarded_callee_gates() {
    // An abortive helper that is BOTH a direct scrutinee AND forwarded-to (called by
    // another E-function `g`) must gate: forwarding the abortive evidence is unsound
    // (its return type is per-handle, not uniform) — it traps on a cross-type forward,
    // or the abort value flows into g's continuation (a silent miscompile, e.g. 1033
    // instead of 33). The abortive constraint now requires every E-function to be
    // reached ONLY as a scrutinee (never a forwarding callee).
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn helper(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x; }\n\
        fn g(x: i64) -> i64 ! { Fail } { let a = helper(x); return a + 1000; }\n\
        fn run() -> i64 { let p = handle helper(0 - 1) { Fail.raise(m) => 11 }; return handle g(0 - 1) { Fail.raise(m) => 22 }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh43_abortive_cross_return_type_forward_gates() {
    // The cross-return-type variant: `helper -> i32` and `g -> i64` both perform the
    // same abortive op and are both scrutinees, but g forwards its `Fn(i32)->i64`
    // evidence into helper which expects `Fn(i32)->i32` — a call_indirect type
    // divergence. Gated (E004) by the no-forwarding-callee constraint.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(c: i32) -> never; }\n\
        fn helper(x: i32) -> i32 ! { Fail } { if x < 0 { perform Fail.raise(7); } return x; }\n\
        fn g(x: i32) -> i64 ! { Fail } { let a: i32 = helper(x); return 999; }\n\
        fn run() -> i64 { let p: i32 = handle helper(0 - 1) { Fail.raise(c) => c }; return handle g(0 - 1) { Fail.raise(c) => 22 }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh43_nested_call_to_e_function_gates() {
    // A call to an E-function in a NON-statement-level position (`h() + 1`) is not
    // reached by the statement-level forwarding walker, so it cannot receive forwarded
    // evidence. The call-count invariant (all_calls != scrutinee + statement-level)
    // catches it and gates (E004) rather than emitting an arity-mismatched call.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Reader { fn get() -> i64; }\n\
        fn h() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        fn g() -> i64 ! { Reader } { return h() + 1; }\n\
        fn run() -> i64 { return handle g() { Reader.get() => resume 5 }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh43c_non_chain_tail_caller_gates() {
    // EH4.3c sweep root: a NON-chain function `bad` (row {Fail, Other}, so excluded
    // from the chain) tail-calls the chain function `deep`. `deep` gets rewritten to
    // return `$EhResult$<H>` + take an `ev` param, but `bad` is never rewritten — its
    // `return deep(...)` would call the rewritten `deep` with the stale signature
    // (non-validating wasm). Now gated (E004): tail calls are only counted from chain
    // functions, so this reach makes `all_calls` exceed `scrutinee + tail`.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        effect Other { fn op() -> i64; }\n\
        fn deep(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x; }\n\
        fn bad(x: i64) -> i64 ! { Fail, Other } { let q = perform Other.op(); return deep(x + q); }\n\
        fn run() -> i64 { let r = handle deep(0 - 4) { Fail.raise(m) => 55 }; return handle bad(0 - 4) { Fail.raise(m) => 77, Other.op() => resume 0 }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh43c_non_chain_tail_caller_abortive_second_effect_gates() {
    // EH4.3c sweep root, abortive-second-effect variant: `q` has row {Fail, Bail}
    // (BOTH abortive), so it is excluded from Fail's chain (row len != 1), yet it
    // tail-calls the chain function `deep`. Like the scoped-second-effect variant,
    // the non-chain caller `q` is never rewritten, so its `return deep(x)` would hit
    // the rewritten `deep` with the stale signature → non-validating wasm. Gated
    // (E004): the fix counts tail calls only from chain functions, regardless of the
    // second effect's flavor.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        effect Bail { fn quit() -> never; }\n\
        fn deep(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x; }\n\
        fn g(x: i64) -> i64 ! { Fail } { return deep(x); }\n\
        fn q(x: i64) -> i64 ! { Fail, Bail } { if x > 999 { perform Bail.quit(); } return deep(x); }\n\
        fn run() -> i64 { let r = handle g(0 - 1) { Fail.raise(m) => 88 }; return handle q(3) { Fail.raise(m) => 0, Bail.quit() => 0 }; }\n";
    assert_has(src, "E004");
}

#[test]
fn eh43d_cross_module_abortive_caller_gates() {
    // EH4.3d ROOT-B: an intra-module abortive-propagation chain in `lib` rewrites
    // `lib::deep`'s ABI (return type → $EhResult, + evidence param). A caller in ANOTHER
    // module (`tool::other`) tail-calls `lib::deep` at the stale signature — invisible to
    // the per-module `lower_abortive_propagation`. Before the fix this compiled to
    // non-validating wasm (the E004 gate only sees surviving handler nodes, not a stale
    // Call). Now the cross-module-reach check gates the effect → its handler nodes survive
    // to E004 (multi-module abortive propagation is deferred, AG-MM-3).
    let src = "#[ring(outer)]\nmodule lib;\n\
        effect Fail { fn raise() -> never; }\n\
        pub fn deep(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(); } return x; }\n\
        fn mid(x: i64) -> i64 ! { Fail } { return deep(x); }\n\
        pub fn run_it(x: i64) -> i64 { let r = handle mid(x) { Fail.raise() => 55 }; return r; }\n\
        #[ring(outer)]\nmodule tool;\n\
        fn other(x: i64) -> i64 ! { Fail } { return lib::deep(x); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let a = lib::run_it(0 - 1); return 0 - a; }\n";
    assert_has(src, "E004");
}
