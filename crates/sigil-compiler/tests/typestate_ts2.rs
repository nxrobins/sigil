//! TS2 of the typestate epic — affine consumption (the security rung).
//!
//! A typestate value (`Grant<Active>`) is classified `AirValueKind::Linear` (its
//! nominal carries a `StateMarker` arg), so the EXISTING `ownership.rs` move-checker
//! fires **O001 use-after-move** when a consumed value is used again. This makes the
//! kernel-doc S1 (use-after-revoke) and S2 (use-after-transfer) scenarios COMPILE
//! ERRORS — a revoked/transferred handle is unusable, with no runtime check.
//!
//! `AirValueKind` drives only the ownership/capability verifiers (never wasm
//! codegen), so this does not perturb the TS0 byte-identical-AIR erasure gate
//! (asserted by the TS0 suite, which must stay green).

use sigil_compiler::compile_tool;

// A capability-lifecycle protocol: delegate → (access | revoke). `revoke` and
// `access` CONSUME the grant by value (a transition / use); a real non-consuming
// reader would take `&Grant<Active>`.
const PROTO: &str = "\
state Grant { Active, Revoked }\n\
record Grant<@S> { id: i64 }\n\
fn delegate() -> Grant<Active> { return Grant { id: 1 }; }\n\
fn revoke(g: Grant<Active>) -> Grant<Revoked> { return Grant { id: 0 }; }\n\
fn access(g: Grant<Active>) -> i64 { return g.id; }\n";

fn codes_of_err(src: &str) -> Vec<String> {
    let err = compile_tool(src).expect_err("expected the program to be rejected");
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect()
}

fn body(stmts: &str) -> String {
    format!(
        "module tool;\n{PROTO}\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{stmts}}}\n"
    )
}

// ── S1: use-after-revoke is a compile error ────────────────────────────────────

#[test]
fn use_after_revoke_is_o001() {
    // `revoke(g)` CONSUMES `g` (by value, Linear); the later `access(g)` is a
    // use-after-move. `g` is still type `Grant<Active>`, so this is NOT a state
    // mismatch (T266) — it isolates the AFFINE check (O001).
    let src = body(
        "    let g: Grant<Active> = delegate();\n\
         \x20   let r: Grant<Revoked> = revoke(g);\n\
         \x20   let x: i64 = access(g);\n\
         \x20   return x;\n",
    );
    let cs = codes_of_err(&src);
    assert!(
        cs.iter().any(|c| c == "O001"),
        "use-after-revoke must be O001 (use after move); got {cs:?}"
    );
}

#[test]
fn double_consume_is_o001() {
    // Consuming the same grant twice — the second `revoke(g)` uses a moved value.
    let src = body(
        "    let g: Grant<Active> = delegate();\n\
         \x20   let r1: Grant<Revoked> = revoke(g);\n\
         \x20   let r2: Grant<Revoked> = revoke(g);\n\
         \x20   return r1.id;\n",
    );
    let cs = codes_of_err(&src);
    assert!(
        cs.iter().any(|c| c == "O001"),
        "double-consume of a typestate value must be O001; got {cs:?}"
    );
}

// ── the legal single-consume lifecycle compiles ────────────────────────────────

#[test]
fn legal_single_consume_compiles() {
    // `g` is consumed exactly once (by `revoke`); `r` is used once. No double-use,
    // so the affine check passes and the program compiles + lowers to wasm.
    let src = body(
        "    let g: Grant<Active> = delegate();\n\
         \x20   let r: Grant<Revoked> = revoke(g);\n\
         \x20   return r.id;\n",
    );
    assert!(
        compile_tool(&src).is_ok(),
        "the legal single-consume lifecycle must compile: {:?}",
        compile_tool(&src).err().map(|e| e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect::<Vec<_>>())
    );
}
