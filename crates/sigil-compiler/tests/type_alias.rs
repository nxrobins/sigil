//! PR-E4: type aliases `type Name = TypeExpr;` — substitutive resolution,
//! transitivity through alias chains, the cyclic-alias guard (T263, no hang), and
//! end-to-end compilation. This is the Rust reference-compiler side; self-hosted
//! parity lands in the parser/typecheck differentials.

use sigil_compiler::diagnostics::Severity;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileOptions, compile_tool, name_resolution, parser, type_check};

/// Every ERROR-severity diagnostic code for `src` (parse → name-resolve → check).
fn error_codes(src: &str) -> Vec<String> {
    let source = SourceFile::new("alias.sigil", src);
    let (ast, pdiags) = parser::parse(&source);
    let mut codes: Vec<String> = pdiags
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| d.code().as_str().to_string())
        .collect();
    match name_resolution::resolve(&ast) {
        Err(rdiags) => codes.extend(
            rdiags
                .iter()
                .filter(|d| d.severity() == Severity::Error)
                .map(|d| d.code().as_str().to_string()),
        ),
        Ok(resolved) => {
            let (_t, _r, diags) =
                type_check::check_collecting(&resolved, &CompileOptions::default());
            codes.extend(
                diags
                    .iter()
                    .filter(|d| d.severity() == Severity::Error)
                    .map(|d| d.code().as_str().to_string()),
            );
        }
    }
    codes
}

#[test]
fn alias_resolves_to_underlying_scalar() {
    // `NodeId` resolves to i64 — `n + 1` (i64 arithmetic) + an i64 return type-check
    // clean. Were the alias left opaque (`Named("NodeId")`), `n + 1` would error, so a
    // clean result PROVES the substitution happened.
    let src = "module m;\ntype NodeId = i64;\npub fn f(n: NodeId) -> i64 { return n + 1; }\n";
    assert!(
        error_codes(src).is_empty(),
        "alias-to-i64 should type-check clean: {:?}",
        error_codes(src)
    );
}

#[test]
fn alias_chain_resolves_transitively() {
    // `type A = B; type B = i64` ⇒ A is i64 (transitive expansion).
    let src = "module m;\ntype A = B;\ntype B = i64;\npub fn f(x: A) -> i64 { return x; }\n";
    assert!(
        error_codes(src).is_empty(),
        "transitive alias chain should resolve to i64: {:?}",
        error_codes(src)
    );
}

#[test]
fn self_cyclic_alias_emits_t263_without_hanging() {
    // `type A = A;` is cyclic — T263, the alias resolves to an opaque type (no infinite
    // recursion). Reaching the assert at all proves there was no hang.
    let src = "module m;\ntype A = A;\npub fn f() -> i64 { return 0; }\n";
    assert!(
        error_codes(src).contains(&"T263".to_string()),
        "self-cyclic alias must emit T263: {:?}",
        error_codes(src)
    );
}

#[test]
fn mutual_cyclic_alias_emits_t263_without_hanging() {
    // `type A = B; type B = A;` — both on the cycle; T263, no hang.
    let src = "module m;\ntype A = B;\ntype B = A;\npub fn f() -> i64 { return 0; }\n";
    assert!(
        error_codes(src).contains(&"T263".to_string()),
        "mutually-cyclic aliases must emit T263: {:?}",
        error_codes(src)
    );
}

#[test]
fn alias_compiles_end_to_end() {
    // The whole pipeline (parse → resolve → type-check → AIR → wasm): an alias-typed
    // local resolves to i64 and compiles to a runnable tool.
    let src = "module tool;\ntype Count = i64;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { let c: Count = 5; return c; }\n";
    assert!(
        compile_tool(src).is_ok(),
        "an alias-typed program should compile end-to-end"
    );
}
