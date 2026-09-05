//! Regression: a reserved keyword used where an identifier (a name) is
//! required must produce a uniform `P026` diagnostic with FAITHFUL recovery —
//! never a silent degenerate parse that truncates the module and type-checks
//! clean.
//!
//! Bug report (2026-06-13): `module demo; fn handle(x: i64) -> i64 { ... }`
//! parsed into a 0-item module plus a synthetic `init` Unit function that
//! `check_with_options` accepted — dropping (and so masking the errors in)
//! everything after `handle`. `handle` is a reserved keyword (the effect
//! handler `handle E { ... }`); the same held for `spawn`, `on`, `cap`, etc.
//! The fix recognises a reserved keyword in any identifier position, emits a
//! precise `P026`, consumes the keyword, and continues parsing — so the rest
//! of the program survives and is type-checked faithfully.

use sigil_compiler::CompileOptions;
use sigil_compiler::diagnostics::Severity;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{name_resolution, parser, type_check};

fn parse_error_codes(src: &str) -> Vec<String> {
    let source = SourceFile::new("<test>", src);
    let (_ast, diags) = parser::parse(&source);
    diags
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| d.code().as_str().to_owned())
        .collect()
}

fn module_item_count(src: &str) -> usize {
    let source = SourceFile::new("<test>", src);
    let (ast, _diags) = parser::parse(&source);
    ast.modules.iter().map(|m| m.items.len()).sum()
}

/// True only if the whole pipeline accepts the program (resolution Ok AND
/// type-check Ok) — i.e. the harness-style "graceful oracle" view that
/// ignores parse diagnostics. The bug made this return `true` on a truncated
/// AST; the fix makes it return `false` whenever a dropped item carried an
/// error.
fn graceful_oracle_accepts(src: &str) -> bool {
    let source = SourceFile::new("<test>", src);
    let (ast, _diags) = parser::parse(&source);
    let resolved = match name_resolution::resolve(&ast) {
        Ok(r) => r,
        Err(_) => return false,
    };
    type_check::check_with_options(&resolved, &CompileOptions::default()).is_ok()
}

#[test]
fn fn_name_reserved_keyword_emits_p026_without_truncation() {
    // The original bug repro (with the trailing call removed so the only
    // signal is the fn-name position).
    let src = "module demo; fn handle(x: i64) -> i64 { return x; } \
               pub fn f() -> i64 { return 1; }";
    let codes = parse_error_codes(src);
    assert!(
        codes.contains(&"P026".to_owned()),
        "expected a P026 reserved-keyword diagnostic, got {codes:?}",
    );
    // No truncation: BOTH functions survive as items. The bug dropped this to
    // a single synthetic `init` (0 source items).
    assert_eq!(
        module_item_count(src),
        2,
        "the module was truncated — items after the reserved keyword were lost",
    );
}

#[test]
fn type_error_after_reserved_keyword_is_not_masked() {
    // The dangerous case the report calls out: before the fix, `fn handle`
    // truncated the module and the synthetic init type-checked clean,
    // MASKING the blatant type error in the following function. Now the
    // following function is parsed faithfully and its error is caught.
    let src = "module demo; fn handle(x: i64) -> i64 { return x; } \
               pub fn bad() -> i64 { return true; }";
    assert!(
        !graceful_oracle_accepts(src),
        "a real type error after a reserved keyword was masked by truncation",
    );
    assert!(parse_error_codes(src).contains(&"P026".to_owned()));
    assert_eq!(module_item_count(src), 2);
}

#[test]
fn param_position_emits_p026() {
    let src = "module demo; pub fn f(handle: i64) -> i64 { return 1; }";
    let codes = parse_error_codes(src);
    assert!(
        codes.contains(&"P026".to_owned()),
        "parameter-name position did not emit P026, got {codes:?}",
    );
    // The function is not dropped.
    assert_eq!(module_item_count(src), 1);
}

#[test]
fn let_binding_position_emits_p026() {
    let src = "module demo; pub fn f() -> i64 { let spawn: i64 = 5; return 1; }";
    let codes = parse_error_codes(src);
    assert!(
        codes.contains(&"P026".to_owned()),
        "let-binding position did not emit P026, got {codes:?}",
    );
    assert_eq!(module_item_count(src), 1);
}

#[test]
fn reserved_keywords_are_uniform_in_fn_name_position() {
    // Every actor/effect-grammar keyword the report flagged behaves the same:
    // a P026 diagnostic and a faithfully-parsed, non-truncated module.
    for kw in [
        "handle", "spawn", "on", "ring", "send", "ask", "region", "cap", "actor", "effect",
    ] {
        let src = format!(
            "module demo; fn {kw}(x: i64) -> i64 {{ return x; }} \
             fn second() -> i64 {{ return 1; }}"
        );
        let codes = parse_error_codes(&src);
        assert!(
            codes.contains(&"P026".to_owned()),
            "`{kw}` in fn-name position did not emit P026, got {codes:?}",
        );
        assert_eq!(
            module_item_count(&src),
            2,
            "`{kw}` truncated the module instead of recovering faithfully",
        );
    }
}

#[test]
fn legitimate_identifiers_are_unaffected() {
    // `handler` and `reply` are NOT keywords — they must parse cleanly and
    // the valid program must type-check.
    let src = "module demo; fn handler(x: i64) -> i64 { return x; } \
               pub fn f() -> i64 { return handler(1); }";
    let codes = parse_error_codes(src);
    assert!(
        codes.is_empty(),
        "a legitimate identifier was wrongly rejected: {codes:?}",
    );
    assert!(
        graceful_oracle_accepts(src),
        "a valid program using `handler` was rejected",
    );
}
