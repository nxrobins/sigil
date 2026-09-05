//! DEF-2a PR-1 — the region-escape gate (T254).
//!
//! A value heap-allocated inside a `region {}` block (birth-depth `d > 0`) may not
//! flow to a sink that outlives the region (`reject ⟺ birth_depth > scope_depth`):
//! the region's memory is reclaimed at block exit, so the alias would dangle.
//!
//! `region {}` is STATEMENT-only in SIGIL (it is not accepted as a `let` RHS or a
//! block-tail value), so its own last-expression value is always discarded — the
//! escapes that matter are body-internal: a region value flowing OUT via a
//! call/method argument or an assignment into a longer-lived place. (Hence there is
//! no "result sink"; one would only over-reject a safely-discarded heap construct.)
//! Scoring is over EXPRESSIONS, not just let-bound locals (NC-R3), and fail-closed
//! (NC-R4). v1 is CONSERVATIVE — a region value may not reach ANY function yet (the
//! allowlist that makes `v.push(x)` legal is PR-2). Scalars copied out stay legal.

use sigil_compiler::compile_tool;

/// Wrap a function body `body` (which may contain a `region {}`) in a module with a
/// `Point` record + a `sink` helper, compile, and return the diagnostic codes.
fn codes(body: &str) -> Vec<String> {
    let src = format!(
        "module tool;\n\
         record Point {{ x: i64, y: i64 }}\n\
         fn sink(p: Point) -> i64 {{ return p.x; }}\n\
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

fn rejects_t254(body: &str) -> bool {
    codes(body).iter().any(|c| c == "T254")
}

fn compiles_clean(body: &str) -> bool {
    codes(body).is_empty()
}

// ── escapes (T254) ────────────────────────────────────────────────────────────

#[test]
fn region_value_into_call_is_t254() {
    // The call-argument sink: a let-bound region value passed to a function (which
    // could store it past the region) — the canonical body-internal escape.
    assert!(rejects_t254(
        "region buf(64) { let p: Point = Point { x: 1, y: 2 }; let _r: i64 = sink(p); }; return 0;"
    ));
}

#[test]
fn inline_region_value_into_call_is_t254() {
    // NC-R3: an inline construct never bound to a `let` is still scored + caught.
    assert!(rejects_t254(
        "region buf(64) { let _r: i64 = sink(Point { x: 1, y: 2 }); }; return 0;"
    ));
}

#[test]
fn region_value_assigned_up_is_t254() {
    // The assignment-RHS sink: storing a region value into a longer-lived local.
    assert!(rejects_t254(
        "let mut outer: Point = Point { x: 0, y: 0 }; \
         region buf(64) { outer = Point { x: 1, y: 2 }; }; return outer.x;"
    ));
}

#[test]
fn region_alias_then_escape_is_t254() {
    // NC-R3 inheritance: a `let`-bound alias of a region value inherits its depth,
    // so escaping the alias (`sink(q)`) is the same escape.
    assert!(rejects_t254(
        "region buf(64) { let p: Point = Point { x: 1, y: 2 }; let q: Point = p; \
         let _r: i64 = sink(q); }; return 0;"
    ));
}

// ── positives (compile clean) ─────────────────────────────────────────────────

#[test]
fn region_scalar_body_compiles() {
    // A pure-scalar region body (the pre-existing pattern) is unaffected.
    assert!(compiles_clean(
        "region buf(64) { let x: i64 = 42; let _y: i64 = x + 1; }; return 0;"
    ));
}

#[test]
fn allocate_and_read_scalar_in_region_compiles() {
    // Allocate a heap value in the region, read a SCALAR (a copy) out of it, discard
    // the value — safe: the heap value is reclaimed unaliased; only the i64 survives.
    assert!(compiles_clean(
        "region buf(64) { let p: Point = Point { x: 7, y: 0 }; let _n: i64 = p.x; }; return 0;"
    ));
}

#[test]
fn discarding_a_heap_result_in_region_compiles() {
    // A region whose last statement constructs a heap value (discarded) is SAFE — the
    // value is reclaimed unaliased. Proves there is NO over-rejecting result sink
    // (`region {}` is statement-only, so the value can never be bound or returned).
    assert!(compiles_clean(
        "region buf(64) { Point { x: 1, y: 2 }; }; return 0;"
    ));
}

#[test]
fn outer_value_used_inside_region_compiles() {
    // "Point up, never down": an OUTER value (depth 0) read inside an inner region
    // has a lower birth-depth than the region's sinks, so it never trips the gate.
    assert!(compiles_clean(
        "let o: Point = Point { x: 5, y: 6 }; region buf(64) { let _n: i64 = o.x; }; return o.x;"
    ));
}

#[test]
fn passing_an_outer_value_from_inside_a_region_compiles() {
    // An OUTER value (depth 0) passed to a function from inside a region is fine —
    // only a region-BORN value is rejected, proving the gate keys on depth, not on
    // "any aliasable argument inside a region".
    assert!(compiles_clean(
        "let o: Point = Point { x: 5, y: 6 }; region buf(64) { let _r: i64 = sink(o); }; return o.x;"
    ));
}
