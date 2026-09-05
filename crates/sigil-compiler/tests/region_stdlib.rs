//! DEF-2a PR-2 — the stdlib receiver-allowlist (NC-R2), the keystone enabler.
//!
//! v1's ONE exemption to "a region value reaches no function" (PR-1) is the RECEIVER
//! position of an allowlisted self-containing stdlib collection method — the `Vec`/`Map`
//! `@ReadOnly` reads and the audited in-place mutators (`push`/`set`/`insert`). This is
//! what makes the keystone — fill + read a region-scoped `Vec`/`Map` — compile:
//!
//! ```text
//! region r(N) { let v: Vec<i64> = Vec::new(); v.push(x); … let n = v.get(i); v.len(); }
//! ```
//!
//! Every OTHER function flow stays a T254 escape: a whole region collection passed to a
//! free/user function (the callee could store it), a user-defined method on a region
//! value, and — critically (NC-R2, the store-after-reclaim UAF) — a region-born element
//! appended into a longer-lived collection, which is caught by checking each non-self
//! ARG at the RECEIVER's depth (`reject ⟺ birth_depth(arg) > recv_depth`). A
//! same-or-longer-lived arg into a shorter-lived region collection is fine.
//!
//! The closed allowlist itself is pinned by the `region_allowlist_is_closed` unit test
//! in `type_check/statements.rs` (the `vec_quarantine` analogue).

use sigil_compiler::compile_tool;

/// Module skeleton: a `Point` record with a (non-allowlisted) user method `describe`, a
/// free fn `vsink` taking a `Vec`, and `body` spliced into `f`. Mentioning `Vec`
/// triggers ambient stdlib injection. Returns the emitted diagnostic codes (empty ⇒
/// clean compile).
fn codes(body: &str) -> Vec<String> {
    let src = format!(
        "module tool;\n\
         record Point {{ x: i64, y: i64 }}\n\
         impl Point {{ pub fn describe(self: Point) -> i64 {{ return self.x; }} }}\n\
         fn vsink(v: Vec<i64>) -> i64 ! {{ Alloc }} {{ return v.len(); }}\n\
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

// ── the keystone: a region-scoped Vec is fully usable ───────────────────────────

#[test]
fn keystone_region_vec_fill_and_read_compiles() {
    // The whole point of PR-2: allocate a `Vec` in a region, fill it (allowlisted
    // mutator `push`), and read it (allowlisted reads `get`/`len`) — all legal, because
    // each method provably keeps `self` in-region.
    assert!(compiles_clean(
        "region buf(64) { let v: Vec<i64> = Vec::new(); v.push(1); v.push(2); \
         let _n: i64 = v.get(0); let _len: i64 = v.len(); }; return 0;"
    ));
}

// ── rejections: every non-allowlisted flow stays T254 ───────────────────────────

#[test]
fn region_vec_into_free_fn_is_t254() {
    // A whole region `Vec` passed to a user function (not on the allowlist) — the callee
    // could store it past the region.
    assert!(rejects_t254(
        "region buf(64) { let v: Vec<i64> = Vec::new(); v.push(1); let _n: i64 = vsink(v); }; \
         return 0;"
    ));
}

#[test]
fn region_value_user_method_is_t254() {
    // A user-defined method (`Point::describe`) on a region value — NOT on the stdlib
    // allowlist, so the receiver is the conservative scope-0 sink.
    assert!(rejects_t254(
        "region buf(64) { let p: Point = Point { x: 1, y: 2 }; let _n: i64 = p.describe(); }; \
         return 0;"
    ));
}

#[test]
fn storing_region_value_into_outer_vec_is_t254() {
    // NC-R2 — the store-after-reclaim UAF: pushing a region-born element into a
    // longer-lived (outer, depth 0) `Vec` is rejected even though `push` is allowlisted,
    // because the ARG is checked at the receiver's shallower depth (`1 > 0`).
    assert!(rejects_t254(
        "let mut ov: Vec<Point> = Vec::new(); \
         region buf(64) { let p: Point = Point { x: 1, y: 2 }; ov.push(p); }; return 0;"
    ));
}

// ── positives: same-or-longer-lived args into a region collection ────────────────

#[test]
fn same_region_push_of_record_compiles() {
    // Receiver and arg born in the SAME region (depth 1 each): `1 > 1` is false, so
    // appending a same-region element into a same-region `Vec` is allowed.
    assert!(compiles_clean(
        "region buf(64) { let v: Vec<Point> = Vec::new(); let p: Point = Point { x: 1, y: 2 }; \
         v.push(p); }; return 0;"
    ));
}

#[test]
fn pushing_an_outer_value_into_a_region_vec_compiles() {
    // A longer-lived (outer, depth 0) value stored into a shorter-lived region `Vec` is
    // fine — it outlives the container, so nothing dangles (`0 > 1` is false).
    assert!(compiles_clean(
        "let o: Point = Point { x: 5, y: 6 }; \
         region buf(64) { let v: Vec<Point> = Vec::new(); v.push(o); }; return o.x;"
    ));
}
