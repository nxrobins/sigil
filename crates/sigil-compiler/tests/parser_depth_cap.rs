//! Finding P1 regression: the parser's recursive descent must be depth-
//! bounded. Before the S007 cap, a few hundred nested parens (or ~1000
//! unary operators) — a source far under the 5 MB cap — overflowed the
//! stack and aborted the whole process. These tests assert the parser now
//! raises S007 instead. Crucially, the tests *completing at all* (rather
//! than aborting the test binary with a stack overflow) is the core
//! assertion: an unbounded parser would take the process down with it.

use sigil_compiler::compile_named_module;

fn wrap_expr(expr: &str) -> String {
    format!(
        "module sigil;\n\
         entry actor Main {{\n\
         \x20   on Tick() -> i64 {{\n\
         \x20       let r: i64 = {expr};\n\
         \x20       return 1;\n\
         \x20   }}\n\
         }}\n"
    )
}

fn emitted_codes(source: String) -> Vec<String> {
    // `cargo test` runs each test on a spawned thread whose default stack
    // (~2 MB) is far smaller than the main-thread stack (8 MB) the CLI/MCP
    // actually parse on — and where the depth cap was tuned. Run the compile
    // on a thread with a generous stack so this test reproduces the real
    // deployment: the S007 cap must fire long before the stack is exhausted.
    // If the cap ever regressed, the thread would stack-overflow and abort
    // the whole test process — which is itself the failure signal.
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(
            move || match compile_named_module("depth_cap".to_string(), source) {
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
        .expect("parse thread panicked")
}

#[test]
fn deeply_nested_parens_raise_s007_not_stack_overflow() {
    // ~5000 deep: without the cap this reliably stack-overflowed.
    let expr = format!("{}1{}", "(".repeat(5000), ")".repeat(5000));
    let codes = emitted_codes(wrap_expr(&expr));
    assert!(
        codes.iter().any(|c| c == "S007"),
        "expected S007 for deep paren nesting, got {codes:?}"
    );
}

#[test]
fn deep_unary_chain_raises_s007_not_stack_overflow() {
    // ~5000 unary minus: the other reported overflow vector.
    let expr = format!("{}1", "-".repeat(5000));
    let codes = emitted_codes(wrap_expr(&expr));
    assert!(
        codes.iter().any(|c| c == "S007"),
        "expected S007 for deep unary chain, got {codes:?}"
    );
}

#[test]
fn moderate_nesting_is_accepted() {
    // Well under the cap — must still compile cleanly, so the cap does not
    // regress ordinary (even generously nested) code.
    let expr = format!("{}1{}", "(".repeat(32), ")".repeat(32));
    let codes = emitted_codes(wrap_expr(&expr));
    assert!(
        !codes.iter().any(|c| c == "S007"),
        "moderate nesting must not trip the depth cap, got {codes:?}"
    );
}

#[test]
fn deeply_nested_if_statements_raise_s007_not_stack_overflow() {
    // `if true { if true { … return 1; … } }` — statement-BLOCK nesting, a
    // recursion path (block → statement → if → block) entirely separate from
    // expression nesting. Before the block guard this still overflowed.
    let n = 5000;
    let src = format!(
        "module sigil;\nentry actor Main {{\n  on Tick() -> i64 {{\n{}    return 1;\n{}  }}\n}}\n",
        "    if true {\n".repeat(n),
        "    }\n".repeat(n),
    );
    let codes = emitted_codes(src);
    assert!(
        codes.iter().any(|c| c == "S007"),
        "deep if-statement nesting must raise S007, got {codes:?}"
    );
}

#[test]
fn deeply_nested_type_expression_raises_s007_not_stack_overflow() {
    // `let r: (((( … i64 … )))) = 1;` — type-expression grouping nesting, which
    // recurses through parse_type_expr, again separate from expression nesting.
    let n = 5000;
    let ty = format!("{}i64{}", "(".repeat(n), ")".repeat(n));
    let src = format!(
        "module sigil;\nentry actor Main {{\n  on Tick() -> i64 {{\n    let r: {ty} = 1;\n    return 1;\n  }}\n}}\n"
    );
    let codes = emitted_codes(src);
    assert!(
        codes.iter().any(|c| c == "S007"),
        "deep type-expression nesting must raise S007, got {codes:?}"
    );
}
