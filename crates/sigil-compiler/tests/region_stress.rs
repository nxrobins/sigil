//! DEF-2a PR-4 — nested-region polish + stress.
//!
//! Hardens the birth-depth lattice now that PR-1 (the gate), PR-2 (the receiver
//! allowlist), and PR-3 (the `@SecretCT` composition) are in place. The single rule —
//! `reject ⟺ birth_depth(value) > scope_depth(sink)`, "point up, never down" — is
//! exercised across the cases the earlier suites did not reach: genuine NESTING (2- and
//! 3-deep), the inner↔outer direction through the PR-2 arg-at-receiver-depth check,
//! sibling regions + prune-on-exit (NC-R5), the fail-closed provenance join (NC-R4), and
//! the `@SecretCT` axis under nesting.
//!
//! ## Two findings that shaped this suite (empirically verified, see the PR)
//!
//!   * **No value-position branch expressions, and no control-flow in region bodies.**
//!     SIGIL has no `let x = if c { a } else { b }` / `match`-as-expression, and an `if`
//!     STATEMENT inside a `region {}` is rejected by T068. So the plan's "branch-
//!     expression mixed provenance" is not expressible. The NC-R4 fail-closed join is
//!     instead reached through CALL RESULTS: an aliasable call result evaluated inside a
//!     region has no single rooted depth, so it is conservatively region-born
//!     (`current_region_depth`) — proven here.
//!   * **Nested regions work.** `region a { region b { … } }` parses, type-checks, and
//!     increments birth-depth per level, so a depth-2 value escaping to a depth-1 or
//!     depth-0 sink is caught.

use sigil_compiler::compile_tool;

/// Stress harness. `Point` + a `@Public` `sink`, a `@SecretCT` `ssink`, and `make()` — an
/// aliasable-returning free fn used to exercise the fail-closed call-result provenance.
fn codes(body: &str) -> Vec<String> {
    let src = format!(
        "module tool;\n\
         record Point {{ x: i64, y: i64 }}\n\
         fn sink(p: Point) -> i64 {{ return p.x; }}\n\
         fn ssink(p: Point @SecretCT) -> i64 @SecretCT {{ return p.x; }}\n\
         fn make() -> Point ! {{ Alloc }} {{ return Point {{ x: 9, y: 9 }}; }}\n\
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

// ── the depth lattice: nesting + the point-up matrix ─────────────────────────────

#[test]
fn inner_region_value_escapes_to_function_is_t254() {
    // Depth 2 → scope 0: a value born in the INNER of two nested regions, escaping via a
    // call, dangles hardest of all — caught by `2 > 0`.
    assert!(rejects_t254(
        "region a(64) { region b(64) { let p: Point = Point { x: 1, y: 2 }; \
         let _r: i64 = sink(p); }; }; return 0;"
    ));
}

#[test]
fn three_deep_inner_value_escapes_is_t254() {
    // Depth 3 → scope 0: the lattice increments per nesting level; a 3-deep value still
    // cannot reach function lifetime.
    assert!(rejects_t254(
        "region a(64) { region b(64) { region c(64) { let p: Point = Point { x: 1, y: 2 }; \
         let _r: i64 = sink(p); }; }; }; return 0;"
    ));
}

#[test]
fn inner_region_element_into_outer_region_vec_is_t254() {
    // The inner→outer direction (depth 2 → depth 1), via the PR-2 arg-at-receiver-depth
    // check: a depth-2 element appended into a depth-1 `Vec` would dangle when the inner
    // region is reclaimed (`birth_depth(arg)=2 > recv_depth=1`). The receiver `v` is
    // exempt (allowlisted); the ARG is what's rejected.
    assert!(rejects_t254(
        "region a(64) { let v: Vec<Point> = Vec::new(); \
         region b(64) { let p: Point = Point { x: 1, y: 2 }; v.push(p); }; }; return 0;"
    ));
}

#[test]
fn outer_region_element_into_inner_region_vec_compiles() {
    // The opposite direction (depth 1 → depth 2) is SAFE: a longer-lived element stored
    // into a shorter-lived inner `Vec` outlives the container (`1 > 2` is false). Proves
    // the gate is directional, not "any cross-region push".
    assert!(compiles_clean(
        "region a(64) { let p: Point = Point { x: 1, y: 2 }; \
         region b(64) { let v: Vec<Point> = Vec::new(); v.push(p); }; }; return 0;"
    ));
}

#[test]
fn outer_region_value_used_in_inner_region_compiles() {
    // "Point up": a depth-1 value READ inside a depth-2 region never trips the gate — its
    // birth-depth is lower than the inner sinks.
    assert!(compiles_clean(
        "region a(64) { let p: Point = Point { x: 1, y: 2 }; \
         region b(64) { let _n: i64 = p.x; }; }; return 0;"
    ));
}

#[test]
fn inner_region_scalar_read_compiles() {
    // A scalar copied out of a depth-2 value, kept in-region, never dangles. Clean.
    assert!(compiles_clean(
        "region a(64) { region b(64) { let p: Point = Point { x: 1, y: 2 }; \
         let _n: i64 = p.x; }; }; return 0;"
    ));
}

// ── sibling regions + prune-on-exit (NC-R5) ──────────────────────────────────────

#[test]
fn sibling_region_escape_is_isolated() {
    // Two sibling regions at the same depth. The first uses its value safely; the second
    // escapes → T254. Prune-on-exit clears the first region's depth-1 entries before the
    // second is entered, so the sibling's escape is judged on its own (not suppressed,
    // not falsely amplified).
    assert!(rejects_t254(
        "region a(64) { let p: Point = Point { x: 1, y: 2 }; let _n: i64 = p.x; }; \
         region b(64) { let q: Point = Point { x: 3, y: 4 }; let _r: i64 = sink(q); }; return 0;"
    ));
}

#[test]
fn outer_value_usable_after_sibling_regions_compiles() {
    // An OUTER (depth-0) value used AFTER two sibling regions is still usable: prune-on-
    // exit removed every region-depth entry, so nothing stale flags the depth-0 value.
    assert!(compiles_clean(
        "let o: Point = Point { x: 5, y: 6 }; \
         region a(64) { let _n: i64 = o.x; }; \
         region b(64) { let _m: i64 = o.y; }; \
         let _r: i64 = sink(o); return o.x;"
    ));
}

// ── fail-closed provenance (NC-R4), reached via call results ─────────────────────

#[test]
fn region_call_result_escape_is_t254() {
    // NC-R4: an aliasable CALL RESULT inside a region has no single rooted depth, so it
    // is conservatively region-born (`current_region_depth`). Escaping it → T254 — even
    // though `make()` actually returns a fresh value; the join only ever RAISES depth, so
    // under-rejection is impossible.
    assert!(rejects_t254(
        "region buf(64) { let p: Point = make(); let _r: i64 = sink(p); }; return 0;"
    ));
}

#[test]
fn region_call_result_scalar_read_compiles() {
    // The same conservatively-region-born call result, read as a scalar and kept in the
    // region, is fine — the copy never dangles.
    assert!(compiles_clean(
        "region buf(64) { let p: Point = make(); let _n: i64 = p.x; }; return 0;"
    ));
}

// ── the @SecretCT axis composes under nesting ────────────────────────────────────

#[test]
fn secret_inner_region_value_escape_is_t254() {
    // PR-3's composition holds at depth: a `@SecretCT` value born in a 2-deep region
    // cannot escape (T254) — secret material physically cannot outlive even an inner
    // region, regardless of nesting.
    assert!(rejects_t254(
        "region a(64) { region b(64) { let p: Point @SecretCT = Point { x: 1, y: 2 }; \
         let _r: i64 @SecretCT = ssink(p); }; }; return 0;"
    ));
}
