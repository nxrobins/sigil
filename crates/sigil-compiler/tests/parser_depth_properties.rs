//! Property fence for the unbounded-untrusted-input class (parser half).
//!
//! Finding P1 (#512) was that the FIRST depth-cap fix guarded only
//! *expression* nesting; nested *statements* (`if{if{…}}`) and nested *type*
//! expressions (`((((i64))))` recurse through separate descent paths that
//! still overflowed the stack — reachable from untrusted MCP input. The fix
//! converged the guard onto three chokepoints (`parse_prefix_expr`,
//! `parse_type_expr`, `parse_braced_block`) that are *claimed* to cover
//! "every" recursive descent position.
//!
//! `parser_depth_cap.rs` pins that claim with four fixed examples. THIS file
//! pins it as a PROPERTY across every recursive grammar position and a swept
//! range of depths: for ANY shape and ANY depth, the parser must
//!   (a) TERMINATE — the test completing at all is the proof; an unbounded
//!       descent takes the whole process down with a stack overflow — and
//!   (b) raise S007 past the cap, while NOT tripping it on shallow input.
//!
//! The point is future-proofing: a new recursive grammar production added
//! without routing through a chokepoint would parse deep input without S007
//! (or overflow), and the matching shape here goes red. That is precisely the
//! regression that shipped in the first P1 fix and was caught only by manual
//! review.

use proptest::prelude::*;
use sigil_compiler::compile_named_module;

/// Compile on a generous-stack thread — `cargo test`/proptest worker threads
/// get a ~2 MB stack, far under the 8 MB main-thread stack the CLI/MCP parse
/// on (where the cap was tuned). A regression that removed a guard must raise
/// S007; if it instead overflowed, THIS thread aborts the whole test process,
/// which is itself the (loud) failure signal. Mirrors `parser_depth_cap.rs`.
fn emitted_codes(source: String) -> Vec<String> {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(
            move || match compile_named_module("depth_prop".to_string(), source) {
                Ok(_) => Vec::new(),
                Err(err) => err
                    .diagnostics()
                    .iter()
                    .map(|d| d.code().as_str().to_string())
                    .collect(),
            },
        )
        .expect("spawn parse thread")
        .join()
        .expect("parse thread panicked (a stack overflow here = an unguarded recursive descent)")
}

fn has_s007(codes: &[String]) -> bool {
    codes.iter().any(|c| c == "S007")
}

/// Wrap an expression as `let r = <expr>;` inside an actor handler body.
fn wrap_expr(expr: &str) -> String {
    format!(
        "module sigil;\nentry actor Main {{\n  on Tick() -> i64 {{\n    let r = {expr};\n    return 1;\n  }}\n}}\n"
    )
}

/// Wrap a type as the annotation of a `let` binding.
fn wrap_type(ty: &str) -> String {
    format!(
        "module sigil;\nentry actor Main {{\n  on Tick() -> i64 {{\n    let r: {ty} = 1;\n    return 1;\n  }}\n}}\n"
    )
}

/// Wrap a statement-block body (already indented lines).
fn wrap_block(open: &str, close: &str) -> String {
    format!(
        "module sigil;\nentry actor Main {{\n  on Tick() -> i64 {{\n{open}    return 1;\n{close}  }}\n}}\n"
    )
}

/// One nesting SHAPE: a name (for failure messages), the recursive-descent
/// chokepoint it exercises, and `render(depth) -> source`. Together these
/// cover every recursive grammar position that must be depth-bounded.
struct Shape {
    name: &'static str,
    chokepoint: &'static str,
    render: fn(usize) -> String,
}

const SHAPES: &[Shape] = &[
    // ── expression chokepoint (parse_prefix_expr) ──
    Shape {
        name: "parenthesized-expr",
        chokepoint: "parse_prefix_expr",
        render: |n| wrap_expr(&format!("{}1{}", "(".repeat(n), ")".repeat(n))),
    },
    Shape {
        name: "unary-minus-chain",
        chokepoint: "parse_prefix_expr",
        render: |n| wrap_expr(&format!("{}1", "-".repeat(n))),
    },
    Shape {
        name: "unary-not-chain",
        chokepoint: "parse_prefix_expr",
        render: |n| wrap_expr(&format!("{}true", "!".repeat(n))),
    },
    Shape {
        name: "nested-array-literal",
        chokepoint: "parse_prefix_expr",
        render: |n| wrap_expr(&format!("{}1{}", "[".repeat(n), "]".repeat(n))),
    },
    Shape {
        name: "nested-borrow",
        chokepoint: "parse_prefix_expr",
        // SPACE-separated `&` (not `"&".repeat(n)`): once `&&`/`||` became real
        // lexer tokens (`AndAnd`/`OrOr`, maximal munch), a tight run of `n`
        // ampersands lexes as `n/2` `AndAnd` tokens, so `parse_prefix_expr`
        // sees `&& 1` and stops at P020 ("expected expression") long before it
        // can nest to the S007 depth cap. A space between each `&` keeps them
        // distinct borrow prefixes — the recursion this shape is meant to
        // exercise — while `1` is unchanged.
        render: |n| wrap_expr(&format!("{}1", "& ".repeat(n))),
    },
    // ── type chokepoint (parse_type_expr) ──
    Shape {
        name: "parenthesized-type",
        chokepoint: "parse_type_expr",
        render: |n| wrap_type(&format!("{}i64{}", "(".repeat(n), ")".repeat(n))),
    },
    Shape {
        name: "nested-fn-type",
        chokepoint: "parse_type_expr",
        render: |n| {
            // Fn(Fn(Fn(i64) -> i64) -> i64) -> i64
            let mut t = String::from("i64");
            for _ in 0..n {
                t = format!("Fn({t}) -> i64");
            }
            wrap_type(&t)
        },
    },
    Shape {
        name: "nested-array-type",
        chokepoint: "parse_type_expr",
        render: |n| wrap_type(&format!("{}i64{}", "[".repeat(n), "; 1]".repeat(n))),
    },
    // ── statement-block chokepoint (parse_braced_block) ──
    Shape {
        name: "nested-if-blocks",
        chokepoint: "parse_braced_block",
        render: |n| wrap_block(&"    if true {\n".repeat(n), &"    }\n".repeat(n)),
    },
    Shape {
        name: "nested-while-blocks",
        chokepoint: "parse_braced_block",
        render: |n| wrap_block(&"    while false {\n".repeat(n), &"    }\n".repeat(n)),
    },
    Shape {
        name: "nested-for-blocks",
        chokepoint: "parse_braced_block",
        render: |n| wrap_block(&"    for i in 0..1 {\n".repeat(n), &"    }\n".repeat(n)),
    },
];

/// A depth this far past `MAX_EXPR_DEPTH` (128) must trap for EVERY shape,
/// regardless of how many depth-units each nesting level consumes.
const DEEP_MIN: usize = 400;
const DEEP_MAX: usize = 2000;
/// A depth this far UNDER the cap must never trip it, for every shape.
const SHALLOW_MAX: usize = 24;

proptest! {
    // Each case spawns a big-stack thread + runs the full compiler front-end,
    // so keep the case count modest; the shape × depth grid is what matters.
    #![proptest_config(ProptestConfig::with_cases(96))]

    /// Past the cap: EVERY recursive grammar position terminates and raises
    /// S007. A shape that reaches a deep nesting WITHOUT S007 has found an
    /// unguarded descent path (the exact P1 regression).
    #[test]
    fn deep_nesting_terminates_and_raises_s007(
        shape_idx in 0usize..SHAPES.len(),
        depth in DEEP_MIN..DEEP_MAX,
    ) {
        let shape = &SHAPES[shape_idx];
        let codes = emitted_codes((shape.render)(depth));
        prop_assert!(
            has_s007(&codes),
            "shape `{}` (chokepoint {}) at depth {depth} did not raise S007 — \
             an unguarded recursive descent, got {codes:?}",
            shape.name, shape.chokepoint,
        );
    }

    /// Under the cap: no shape false-trips S007 (the guard must not reject
    /// ordinary, even generously nested, code).
    #[test]
    fn shallow_nesting_never_trips_s007(
        shape_idx in 0usize..SHAPES.len(),
        depth in 1usize..SHALLOW_MAX,
    ) {
        let shape = &SHAPES[shape_idx];
        let codes = emitted_codes((shape.render)(depth));
        prop_assert!(
            !has_s007(&codes),
            "shape `{}` at shallow depth {depth} false-tripped the depth cap, got {codes:?}",
            shape.name,
        );
    }
}

/// Boundary example (not a property): every shape must straddle the cap —
/// clearly-under does not trap, clearly-over does. Pins that no shape is
/// silently un-nested (e.g. a `render` that collapses), which would make the
/// property vacuously pass.
#[test]
fn every_shape_straddles_the_cap() {
    for shape in SHAPES {
        let under = emitted_codes((shape.render)(8));
        assert_no_s007(shape, &under, 8);
        let over = emitted_codes((shape.render)(1200));
        assert!(
            has_s007(&over),
            "shape `{}` did not raise S007 at depth 1200 — is it actually nesting?",
            shape.name,
        );
    }
}

fn assert_no_s007(shape: &Shape, codes: &[String], depth: usize) {
    assert!(
        !has_s007(codes),
        "shape `{}` false-tripped S007 at shallow depth {depth}, got {codes:?}",
        shape.name,
    );
}
