//! DEF-2b PR-1 — the `Region` handle type + the lexical-name binding.
//!
//! A region is a runtime VALUE typed `Region` (an i64 handle), not a type-level lifetime
//! (LD-1). The lexical `region NAME(LIMIT) { … }` now binds `NAME` as a `Region` value in
//! its body, scored at the current lexical depth (LD-3) — so the handle is usable inside
//! the block (a future `Vec::in_region(NAME)` argument) but CANNOT escape it: passing,
//! returning, or storing it past the block is `T254`, because a handle to a reclaimed
//! region would dangle. `Region` also resolves as a parameter type (no `@in` yet — that
//! is PR-3). The cross-function lift that makes a region value flow into an annotated user
//! function is PR-4.

use sigil_compiler::diagnostics::Severity;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileOptions, compile_tool, name_resolution, parser, type_check};

/// Module skeleton: a `takes_region(r: Region)` free fn (proves `Region` resolves as a
/// param type) + `body` spliced into `f`. Returns the emitted diagnostic codes.
fn codes(body: &str) -> Vec<String> {
    let src = format!(
        "module tool;\n\
         fn takes_region(r: Region) -> i64 {{ return 0; }}\n\
         fn f() -> i64 ! {{ Alloc }} {{ {body} }}\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{ return f(); }}\n"
    );
    match compile_tool(&src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

/// Type-check ONLY (parse → resolve → check) of the same harness — for an ACCEPTED handle
/// flow, whose codegen (lowering a `Region` argument) lands in PR-7, so `compile_tool`
/// would ICE in AIR lowering. Returns the emitted diagnostic codes.
fn tc_codes(body: &str) -> Vec<String> {
    let src = format!(
        "module tool;\n\
         fn takes_region(r: Region) -> i64 {{ return 0; }}\n\
         fn f() -> i64 ! {{ Alloc }} {{ {body} }}\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{ return f(); }}\n"
    );
    let source = SourceFile::new("<region_type>", &src);
    let (ast, parse_diags) = parser::parse(&source);
    let parse_errs: Vec<String> = parse_diags
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| d.code().as_str().to_string())
        .collect();
    if !parse_errs.is_empty() {
        return parse_errs;
    }
    let resolved = match name_resolution::resolve(&ast) {
        Ok(r) => r,
        Err(diags) => {
            return diags
                .iter()
                .map(|d| d.code().as_str().to_string())
                .collect();
        }
    };
    match type_check::check_with_options(&resolved, &CompileOptions::default()) {
        Ok(_) => Vec::new(),
        Err(diags) => diags
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn compiles_clean(body: &str) -> bool {
    codes(body).is_empty()
}

#[test]
fn region_with_named_handle_compiles() {
    // The region NAME is now a bound `Region` handle (not a dead label); a scalar-body
    // region with the binding in scope still compiles.
    assert!(compiles_clean(
        "region r(64) { let n: i64 = 5; let _m: i64 = n + 1; }; return 0;"
    ));
}

#[test]
fn region_handle_threaded_into_region_param_is_accepted() {
    // PR-1 conservatively rejected ANY handle crossing a function boundary; PR-4 (the
    // AG-R2 lift) THREADS a handle passed into a `Region` PARAMETER — an allowed position
    // (NC-2b-2), not an escape, since the callee receives it as a region and cannot store
    // it past its own scope. So `takes_region(r)` now type-checks. (Asserted at TC level —
    // the handle-argument codegen is PR-7; see `region_poly.rs` for the full lift suite,
    // including that a handle still cannot be RETURNED or stored past its region → T254.)
    assert!(
        tc_codes("region r(64) { let _x: i64 = takes_region(r); }; return 0;").is_empty(),
        "got {:?}",
        tc_codes("region r(64) { let _x: i64 = takes_region(r); }; return 0;")
    );
}

#[test]
fn region_param_type_resolves() {
    // `Region` resolves as a parameter type: `takes_region(r: Region)` in the harness is
    // a well-formed declaration (an unused `Region` param is fine), so the module compiles
    // when `f` does not misuse a handle.
    assert!(compiles_clean("return 0;"));
}
