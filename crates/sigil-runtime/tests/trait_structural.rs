//! PR-4 of the trait epic — STRUCTURAL auto-derivation.
//!
//! A user `record` satisfies a trait by simply declaring the trait's method(s)
//! with a matching signature — no `impl Hash for Point` line (heuristic 5). The
//! satisfaction check reuses ordinary method resolution; the method LOWERING for
//! records already works (normal dispatch resolves `Point::hash`). So a bounded
//! generic over a method-bearing record works end to end, with no inline trait
//! decls (ambient injects `traits` on the `: Hash` bound / `.hash(` call).
//!
//! Rejections: a record MISSING the method → T245; a record whose method has the
//! WRONG signature → T246 (CM-T1 exact match).

mod common;

use sigil_compiler::compile_tool;

use common::run_returning_negative as run_neg;

fn tool_with_defs(defs: &str, body: &str) -> String {
    format!(
        "module tool;\n{defs}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg_defs(defs: &str, body: &str) -> i64 {
    run_neg(&tool_with_defs(defs, body))
}

/// True iff the program fails to compile AND the given code appears.
fn fails_with(defs: &str, body: &str, code: &str) -> bool {
    match compile_tool(&tool_with_defs(defs, body)) {
        Ok(_) => false,
        Err(e) => format!("{e:?}").contains(code),
    }
}

const POINT_HASH: &str = "record Point { x: i64, y: i64 }\n\
    impl Point { fn hash(self: Point) -> i64 { return self.x * 31 + self.y; } }\n\
    fn keyed<T: Hash>(k: T) -> i64 { return k.hash(); }";

// ── structural satisfaction + lowering ───────────────────────────────────────

#[test]
fn record_with_hash_satisfies_and_lowers() {
    // Point declares `hash(self: Point) -> i64` — no `impl Hash for Point`. It
    // satisfies `T: Hash` structurally, and the body's `k.hash()` lowers to the
    // user's `Point::hash`. 3*31 + 4 = 97.
    let r = neg_defs(
        POINT_HASH,
        "    let p: Point = Point { x: 3, y: 4 };\n    let r: i64 = keyed(p);\n    return 0 - r;",
    );
    assert_eq!(r, 97);
}

#[test]
fn record_with_hash_and_eq_satisfies_composed_and_eq_lowers() {
    // Point has both `hash` and `eq` (eq compares only `x`). A `<T: Eq>` generic
    // calls `a.eq(b)` — structural Eq + the user's `Point::eq` lowering.
    let defs = "record Point { x: i64, y: i64 }\n\
        impl Point {\n\
        \x20   fn hash(self: Point) -> i64 { return self.x * 31 + self.y; }\n\
        \x20   fn eq(self: Point, other: Point) -> bool { return self.x == other.x; }\n\
        }\n\
        fn same<T: Hash + Eq>(a: T, b: T) -> i64 { if a.eq(b) { return 1; } else { return 0; } }";
    // Point{1,2}.eq(Point{1,9}) compares x (1 == 1) → true → 1.
    let r = neg_defs(
        defs,
        "    let a: Point = Point { x: 1, y: 2 };\n\
         \x20   let b: Point = Point { x: 1, y: 9 };\n\
         \x20   let r: i64 = same(a, b);\n\
         \x20   return 0 - (r + 100);",
    );
    assert_eq!(r, 101); // 100 + 1
}

#[test]
fn record_eq_distinguishes() {
    let defs = "record Point { x: i64, y: i64 }\n\
        impl Point {\n\
        \x20   fn hash(self: Point) -> i64 { return self.x; }\n\
        \x20   fn eq(self: Point, other: Point) -> bool { return self.x == other.x; }\n\
        }\n\
        fn same<T: Hash + Eq>(a: T, b: T) -> i64 { if a.eq(b) { return 1; } else { return 0; } }";
    // x differs (1 vs 2) → not equal → 0.
    let r = neg_defs(
        defs,
        "    let a: Point = Point { x: 1, y: 0 };\n\
         \x20   let b: Point = Point { x: 2, y: 0 };\n\
         \x20   let r: i64 = same(a, b);\n\
         \x20   return 0 - (r + 100);",
    );
    assert_eq!(r, 100); // 100 + 0
}

// ── rejections ───────────────────────────────────────────────────────────────

#[test]
fn record_missing_method_rejected_t245() {
    // NoHash has no `hash` method → structural check fails with "missing method".
    let defs = "record NoHash { v: i64 }\nfn keyed<T: Hash>(k: T) -> i64 { return 0; }";
    let body =
        "    let n: NoHash = NoHash { v: 1 };\n    let r: i64 = keyed(n);\n    return 0 - 1;";
    assert!(
        fails_with(defs, body, "T245"),
        "a record missing the trait method must be T245"
    );
}

#[test]
fn record_wrong_signature_rejected_t246() {
    // Bad has a `hash` method but it returns `bool`, not `i64` → signature
    // mismatch (CM-T1 demands an EXACT match). The keyed body does not call the
    // method, so the only diagnostic is the bound check's T246.
    let defs = "record Bad { v: i64 }\n\
        impl Bad { fn hash(self: Bad) -> bool { return true; } }\n\
        fn keyed<T: Hash>(k: T) -> i64 { return 0; }";
    let body = "    let b: Bad = Bad { v: 1 };\n    let r: i64 = keyed(b);\n    return 0 - 1;";
    assert!(
        fails_with(defs, body, "T246"),
        "a record whose method has the wrong signature must be T246"
    );
}

#[test]
fn record_wrong_arity_rejected_t246() {
    // `hash` taking an extra parameter is also a signature mismatch.
    let defs = "record Bad { v: i64 }\n\
        impl Bad { fn hash(self: Bad, salt: i64) -> i64 { return self.v + salt; } }\n\
        fn keyed<T: Hash>(k: T) -> i64 { return 0; }";
    let body = "    let b: Bad = Bad { v: 1 };\n    let r: i64 = keyed(b);\n    return 0 - 1;";
    assert!(
        fails_with(defs, body, "T246"),
        "a record whose method has the wrong arity must be T246"
    );
}
