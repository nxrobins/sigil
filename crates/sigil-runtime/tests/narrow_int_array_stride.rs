//! Regression: narrow-int (`i32`/`u32`) array literals must store their elements
//! at the ANNOTATED element width, not the i64 default.
//!
//! THE BUG (pre-fix): an all-integer-literal array bound to a narrow-int
//! annotation —
//!
//!     let a: [i32; 5] = [10, 20, 30, 40, 50];
//!
//! had its `IntLit` elements left unresolved through type-check, so the final
//! default-pass rewrote them (and the array's carried `elem_type`) to `i64`.
//! `lower_array_lit` then stored each element at an 8-byte stride (and as an i64
//! value), while EVERY reader — `index_base_and_bounds` (so `a[k]` and the
//! for-in desugar) and `.contains` — used the `[i32; 5]` annotation's 4-byte
//! width. Stride-8 store vs stride-4 read => every `a[k]` for `k > 0` read
//! garbage (`a[0]` survived by coincidence: the low 4 bytes of slot 0 alias the
//! first read). `[i64; N]`, `[bool; N]`, `[f64; N]` were always correct.
//!
//! THE FIX: `resolve_int_literals_in_expr` now narrows an array/slice literal's
//! integer-literal elements AND its `elem_type` to the annotated `T`, so storage
//! stride, the stored value's AIR type, and every reader's width agree at `T`.
//!
//! These tests exercise the previously-corrupt regime directly: indexing at
//! EVERY position and for-in over both `i32` and `u32` literal arrays. The
//! `.contains` half of the fix is covered in `array_contains.rs`.
//!
//! Decode note: SIGIL has no `as` cast and the i64 `tool_main` cannot return a
//! narrow int, so a narrow-int result is asserted via a `bool` comparison routed
//! to the negative sentinel — `1` = the comparison held, `2` = it did not
//! (the same mechanism `array_contains.rs` uses).

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Array indexing and for-in are Alloc-free, so no `! { Alloc }` effect.
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

/// Compile a COMPLETE module source and recover `value` from a `return 0 -
/// value;` negative-sentinel trap. (Mirrors `array_repeat.rs` /
/// `array_contains.rs`.)
fn neg_src(src: &str) -> i64 {
    let result = compile_tool(src).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a clean negative-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected negative sentinel"),
    }
}

/// Run a `return 0 - value;` body (wrapped in `tool_main`) and recover `value`.
fn neg(body: &str) -> i64 {
    neg_src(&tool(body))
}

/// Build a tool from `setup` statements followed by a boolean `cond`, and report
/// whether `cond` held at runtime (`1` sentinel) or not (`2`). This lets a
/// narrow-int value be checked without returning it (no `as` cast exists, and
/// the i64 `tool_main` can't return an i32/u32 directly).
fn holds(setup: &str, cond: &str) -> bool {
    let body = format!("{setup}\n    if {cond} {{ return 0 - 1; }} else {{ return 0 - 2; }}");
    match neg(&body) {
        1 => true,
        2 => false,
        other => panic!("unexpected sentinel {other} (cond `{cond}`)"),
    }
}

/// Like `holds`, but the program carries a `prelude` (extra top-level fns —
/// e.g. a helper that RETURNS a narrow-int array) before `tool_main`. Reports
/// whether `cond` (over the `setup` statements) held.
fn holds_prog(prelude: &str, setup: &str, cond: &str) -> bool {
    let src = format!(
        "module tool;\n{prelude}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n\
         {setup}\n    if {cond} {{ return 0 - 1; }} else {{ return 0 - 2; }}\n}}\n"
    );
    match neg_src(&src) {
        1 => true,
        2 => false,
        other => panic!("unexpected sentinel {other} (cond `{cond}`)"),
    }
}

// ───────────────────────── the exact bug repro ─────────────────────────

#[test]
fn i32_index_three_equals_forty() {
    // The poster child: `a[3]` must be 40. Pre-fix this read garbage and the
    // `==` mismatched, returning 2.
    let body = "    let a: [i32; 5] = [10, 20, 30, 40, 50];\n\
        \x20   let x: i32 = a[3];\n\
        \x20   let e: i32 = 40;\n\
        \x20   if x == e { return 0 - 1; } else { return 0 - 2; }";
    assert_eq!(neg(body), 1, "a[3] must equal 40");
}

// ───────────────────────── i32 indexing at EVERY position ─────────────────────────

#[test]
fn i32_index_each_position() {
    let setup = "    let a: [i32; 5] = [10, 20, 30, 40, 50];";
    assert!(holds(setup, "a[0] == 10"), "i32 a[0]");
    assert!(holds(setup, "a[1] == 20"), "i32 a[1]");
    assert!(holds(setup, "a[2] == 30"), "i32 a[2]");
    assert!(holds(setup, "a[3] == 40"), "i32 a[3]");
    assert!(holds(setup, "a[4] == 50"), "i32 a[4]");
    // Negative control: the read returns SPECIFICALLY 40, not "always true".
    assert!(!holds(setup, "a[3] == 30"), "i32 a[3] is 40, not 30");
}

#[test]
fn i32_sum_via_indexing_is_150() {
    // Only correct if NO slot aliases another (the 8-byte-stride bug made
    // several slots read 0 or each other's high words).
    let setup = "    let a: [i32; 5] = [10, 20, 30, 40, 50];";
    assert!(holds(setup, "(a[0] + a[1] + a[2] + a[3] + a[4]) == 150"));
}

// ───────────────────────── u32 indexing at EVERY position ─────────────────────────

#[test]
fn u32_index_each_position() {
    let setup = "    let a: [u32; 5] = [10, 20, 30, 40, 50];";
    assert!(holds(setup, "a[0] == 10"), "u32 a[0]");
    assert!(holds(setup, "a[1] == 20"), "u32 a[1]");
    assert!(holds(setup, "a[2] == 30"), "u32 a[2]");
    assert!(holds(setup, "a[3] == 40"), "u32 a[3]");
    assert!(holds(setup, "a[4] == 50"), "u32 a[4]");
    assert!(!holds(setup, "a[1] == 10"), "u32 a[1] is 20, not 10");
}

#[test]
fn u32_sum_via_indexing_is_150() {
    let setup = "    let a: [u32; 5] = [10, 20, 30, 40, 50];";
    assert!(holds(setup, "(a[0] + a[1] + a[2] + a[3] + a[4]) == 150"));
}

// ───────────────────────── for-in over a narrow-int array ─────────────────────────

#[test]
fn i32_for_in_sums_every_element() {
    // for-in reads through the same `index_base_and_bounds` width as `a[k]`;
    // a stride mismatch would drop/duplicate elements and skew the sum.
    let setup = "    let a: [i32; 5] = [10, 20, 30, 40, 50];\n\
        \x20   let mut sum: i32 = 0;\n\
        \x20   for x in a {\n\
        \x20       sum = sum + x;\n\
        \x20   }";
    assert!(holds(setup, "sum == 150"), "for-in over i32 array");
}

#[test]
fn u32_for_in_sums_every_element() {
    let setup = "    let a: [u32; 5] = [10, 20, 30, 40, 50];\n\
        \x20   let mut sum: u32 = 0;\n\
        \x20   for x in a {\n\
        \x20       sum = sum + x;\n\
        \x20   }";
    assert!(holds(setup, "sum == 150"), "for-in over u32 array");
}

// ───────────────────────── values that EXPOSE an i64-stride read ─────────────────────────

#[test]
fn i32_distinct_values_each_slot_isolated() {
    // Distinct, non-overlapping values so an 8-byte-strided read (the bug) would
    // surface a *different* wrong number per slot rather than a lucky 0/alias.
    let setup = "    let a: [i32; 4] = [1000, 2000, 3000, 4000];";
    assert!(holds(setup, "a[0] == 1000"), "i32 a[0]");
    assert!(holds(setup, "a[1] == 2000"), "i32 a[1]");
    assert!(holds(setup, "a[2] == 3000"), "i32 a[2]");
    assert!(holds(setup, "a[3] == 4000"), "i32 a[3]");
}

// ───────────────────────── return position (the helper-returns-array twin) ─────────────────────────

#[test]
fn i32_return_value_indexed_by_caller() {
    // A helper RETURNS a narrow-int array literal; the caller indexes it. The
    // return path now resolves the literal's elements to the return type's i32
    // (it didn't before — the return-position twin of the let/arg bug).
    let prelude = "fn helper() -> [i32; 3] { return [10, 20, 30]; }";
    let setup = "    let a: [i32; 3] = helper();";
    assert!(holds_prog(prelude, setup, "a[1] == 20"), "returned a[1]");
    assert!(holds_prog(prelude, setup, "a[2] == 30"), "returned a[2]");
    assert!(holds_prog(prelude, setup, "a[0] == 10"), "returned a[0]");
    // Negative control: a[1] is specifically 20.
    assert!(
        !holds_prog(prelude, setup, "a[1] == 10"),
        "returned a[1] is 20"
    );
}

#[test]
fn u32_return_value_indexed_by_caller() {
    let prelude = "fn helper() -> [u32; 4] { return [11, 22, 33, 44]; }";
    let setup = "    let a: [u32; 4] = helper();";
    assert!(
        holds_prog(prelude, setup, "a[1] == 22"),
        "returned u32 a[1]"
    );
    assert!(
        holds_prog(prelude, setup, "a[3] == 44"),
        "returned u32 a[3]"
    );
}

#[test]
fn u32_return_across_if_branches() {
    // Each `return [..]` inside a branch resolves to the return type's u32.
    let prelude =
        "fn pick(c: bool) -> [u32; 2] { if c { return [10, 20]; } else { return [30, 40]; } }";
    let setup = "    let a: [u32; 2] = pick(false);";
    assert!(holds_prog(prelude, setup, "a[1] == 40"), "else-branch a[1]");
    let setup_t = "    let a: [u32; 2] = pick(true);";
    assert!(
        holds_prog(prelude, setup_t, "a[1] == 20"),
        "then-branch a[1]"
    );
}

// ───────────────────────── the wide-int paths stay correct (regression guard) ─────────────────────────

#[test]
fn i64_array_indexing_unchanged() {
    // `[i64; N]` was always correct (the default IS i64); guard that the fix
    // doesn't perturb it. (i64 returns directly — no sentinel needed.)
    let body = "    let a: [i64; 4] = [10, 20, 30, 40];\n    return 0 - (a[1] + a[3]);";
    assert_eq!(neg(body), 60);
}
