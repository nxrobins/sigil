//! DEF-2b PR-5 — the `where region(a): region(b)` outlives clause.
//!
//! PR-4 made distinct `Param` regions INCOMPARABLE (a region value may flow into an `@in r`
//! param only when it lives in EXACTLY `r`). `where region(a): region(b)` (read "a outlives
//! b", mirroring Rust's `'a: 'b`) is the ONLY thing that makes `Param(a) outlives Param(b)`
//! true for `a != b`. It has two enforced sides:
//!
//!   * CALLEE side — inside the declaring function's body, the relation lets a value living
//!     in `a` flow into a sink living in `b` (`a` is longer-lived, so it cannot dangle).
//!     This FLIPS a `T254` to clean exactly when the clause is present; the reverse
//!     direction stays `T254`; and
//!   * CALLER side (the obligation, NC-2b-4) — a caller of a `where`-bearing function must
//!     pass region arguments that actually satisfy the declared relation, else it cannot
//!     honour the contract the callee's body relies on → `T254`.
//!
//! DIRECT-PAIR-ONLY: the clause is a flat set of edges, no transitive closure (AG-2b-9).
//! The clause occupies the param-`where` position (between the parameter list and `->`).
//!
//! Asserted at the TYPE-CHECK level (`parse → resolve → check`) — like `region_poly.rs`, an
//! accepted region-poly program is type-valid but its `Region`-argument codegen is PR-7, so
//! the full pipeline would ICE in AIR lowering. A user `record` stands in for the region
//! value (single-source, no ambient `Vec`).

use sigil_compiler::diagnostics::Severity;
use sigil_compiler::source::SourceFile;
use sigil_compiler::{CompileOptions, name_resolution, parser, type_check};

fn codes(src: &str) -> Vec<String> {
    let source = SourceFile::new("<region_where>", src);
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

fn has(src: &str, code: &str) -> bool {
    codes(src).iter().any(|c| c == code)
}

// `inner` wants its value `@in b`; `outer` holds a value `@in a` and forwards it to `inner`
// under region `b` — sound iff `a` outlives `b`.
const PRELUDE: &str = "module tool;\n\
     record Box { v: i64 }\n\
     fn inner(b: Region, w: Box @in b) -> i64 { return 0; }\n";

// ── callee side: the clause FLIPS T254 → clean, directionally ─────────────────────

#[test]
fn forwarding_under_a_declared_outlives_is_accepted() {
    // `outer` forwards its `@in a` value into `inner`'s `@in b` parameter. That stores an
    // `a`-region value into a `b`-region sink — sound only because `where region(a):
    // region(b)` declares `a` outlives `b` (`Param(0)` outlives `Param(1)`). Clean.
    let src = format!(
        "{PRELUDE}\
         fn outer(a: Region, b: Region, va: Box @in a) where region(a): region(b) -> i64 \
         {{ return inner(b, va); }}\n"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn forwarding_without_the_clause_is_t254() {
    // The SAME body without the `where` clause: distinct param regions are incomparable, so
    // the `a`-region value cannot enter the `b`-region sink → `T254`. This is the flip the
    // clause performs.
    let src = format!(
        "{PRELUDE}\
         fn outer(a: Region, b: Region, va: Box @in a) -> i64 \
         {{ return inner(b, va); }}\n"
    );
    assert!(has(&src, "T254"), "got {:?}", codes(&src));
}

#[test]
fn the_reverse_outlives_does_not_help_t254() {
    // Direction matters: `where region(b): region(a)` declares `b` outlives `a`, which does
    // NOT license storing an `a`-region value into a `b`-region sink → still `T254`. The
    // edge is directed.
    let src = format!(
        "{PRELUDE}\
         fn outer(a: Region, b: Region, va: Box @in a) where region(b): region(a) -> i64 \
         {{ return inner(b, va); }}\n"
    );
    assert!(has(&src, "T254"), "got {:?}", codes(&src));
}

// ── caller side: the obligation (NC-2b-4) ─────────────────────────────────────────

const OUTER_WITH_WHERE: &str = "fn outer(a: Region, b: Region, va: Box @in a) \
     where region(a): region(b) -> i64 { return inner(b, va); }\n";

#[test]
fn caller_passing_regions_that_satisfy_the_clause_is_accepted() {
    // A caller must pass region arguments where `a` actually outlives `b`. Here `a` is the
    // OUTER lexical region and `b` the inner one (outer outlives inner), and the value lives
    // in the outer region — the obligation is met. Clean.
    let src = format!(
        "{PRELUDE}{OUTER_WITH_WHERE}\
         fn caller() -> i64 ! {{ Alloc }} {{ \
             region rlong(64) {{ let v: Box = Box {{ v: 1 }}; \
                 region rshort(64) {{ let _x: i64 = outer(rlong, rshort, v); }}; \
             }}; return 0; \
         }}\n"
    );
    assert!(codes(&src).is_empty(), "got {:?}", codes(&src));
}

#[test]
fn caller_passing_regions_that_violate_the_clause_is_t254() {
    // The obligation fails when the caller passes a SHORTER region as `a` and a longer one
    // as `b`: `a` (inner `rshort`) does not outlive `b` (outer `rlong`), so the caller
    // cannot honour `where region(a): region(b)` → `T254`. (The per-arg lift alone would
    // pass — this `T254` is the caller-side obligation firing.)
    let src = format!(
        "{PRELUDE}{OUTER_WITH_WHERE}\
         fn caller() -> i64 ! {{ Alloc }} {{ \
             region rlong(64) {{ \
                 region rshort(64) {{ let v: Box = Box {{ v: 1 }}; \
                     let _x: i64 = outer(rshort, rlong, v); }}; \
             }}; return 0; \
         }}\n"
    );
    assert!(has(&src, "T254"), "got {:?}", codes(&src));
}

// ── validation (P025) + composition ───────────────────────────────────────────────

#[test]
fn where_naming_a_non_region_param_is_p025() {
    // Both sides of a `where region(...)` must be `Region` parameters; `x: i64` is not, so
    // `where region(x): region(b)` is rejected at parse → P025.
    let src = "module tool;\n\
         fn f(x: i64, b: Region) where region(x): region(b) -> i64 { return 0; }\n";
    assert!(has(src, "P025"), "got {:?}", codes(src));
}

#[test]
fn where_with_unknown_region_name_is_p025() {
    // A `where region(bogus): region(b)` naming no parameter → P025.
    let src = "module tool;\n\
         fn f(a: Region, b: Region) where region(bogus): region(b) -> i64 { return 0; }\n";
    assert!(has(src, "P025"), "got {:?}", codes(src));
}

#[test]
fn malformed_where_missing_colon_is_p025() {
    // `where region(a) region(b)` (no `:`) is a malformed outlives clause → P025.
    let src = "module tool;\n\
         fn f(a: Region, b: Region) where region(a) region(b) -> i64 { return 0; }\n";
    assert!(has(src, "P025"), "got {:?}", codes(src));
}

#[test]
fn a_plain_value_where_clause_still_parses_as_a_refinement() {
    // Orthogonality: a `where x > 0` refinement-where (no `region` keyword) is untouched by
    // the region-outlives parser and still type-checks as a refinement. Clean.
    let src = "module tool;\n\
         fn f(x: i64) where x > 0 -> i64 { return x; }\n";
    assert!(codes(src).is_empty(), "got {:?}", codes(src));
}
