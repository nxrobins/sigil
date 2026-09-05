//! PR-5 of the trait epic — explicit `impl Trait for Type` + the orphan rule.
//!
//! An explicit `impl Hash for Point { fn hash(self: Point) -> i64 { … } }`
//! attaches the method to `Point` exactly as an inherent `impl Point { … }`, so
//! Point satisfies `Hash` (the methods register; structural satisfaction finds
//! them). The new value is COHERENCE: the orphan rule (AG-T2 structural proxy)
//! rejects an explicit impl whose target is not a record/enum declared in the
//! program — so the built-in primitive impls cannot be overridden — and forbids
//! two impls of the same (trait, type) pair.

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

fn fails_with(defs: &str, body: &str, code: &str) -> bool {
    match compile_tool(&tool_with_defs(defs, body)) {
        Ok(_) => false,
        Err(e) => format!("{e:?}").contains(code),
    }
}

// ── an explicit impl satisfies + lowers ──────────────────────────────────────

#[test]
fn explicit_impl_satisfies_and_lowers() {
    // `impl Hash for Point` (explicit) attaches Point::hash; Point satisfies
    // `T: Hash` and `k.hash()` lowers to it. 3*31 + 4 = 97.
    let defs = "record Point { x: i64, y: i64 }\n\
        impl Hash for Point { fn hash(self: Point) -> i64 { return self.x * 31 + self.y; } }\n\
        fn keyed<T: Hash>(k: T) -> i64 { return k.hash(); }";
    let r = neg_defs(
        defs,
        "    let p: Point = Point { x: 3, y: 4 };\n    let r: i64 = keyed(p);\n    return 0 - r;",
    );
    assert_eq!(r, 97);
}

#[test]
fn inherent_impl_still_works_after_for_parsing() {
    // Regression: `impl Point { … }` (no `for`) is unchanged by the `for` branch.
    let defs = "record Point { x: i64, y: i64 }\n\
        impl Point { fn hash(self: Point) -> i64 { return self.x * 31 + self.y; } }\n\
        fn keyed<T: Hash>(k: T) -> i64 { return k.hash(); }";
    let r = neg_defs(
        defs,
        "    let p: Point = Point { x: 3, y: 4 };\n    let r: i64 = keyed(p);\n    return 0 - r;",
    );
    assert_eq!(r, 97);
}

// ── the orphan rule (AG-T2 structural proxy) ─────────────────────────────────

#[test]
fn orphan_impl_for_i64_is_t249() {
    // `impl Hash for i64` — i64 is a primitive, not a declared record/enum. The
    // built-in `i64: Hash` is unoverridable; this is an orphan violation.
    let defs = "impl Hash for i64 { fn hash(self: i64) -> i64 { return self; } }";
    assert!(
        fails_with(defs, "    return 0 - 1;", "T249"),
        "an explicit impl for a primitive must be T249"
    );
}

#[test]
fn orphan_impl_for_str_is_t249() {
    let defs = "impl Eq for str { fn eq(self: str, other: str) -> bool { return true; } }";
    assert!(fails_with(defs, "    return 0 - 1;", "T249"));
}

// ── coherence: no duplicate impls ────────────────────────────────────────────

#[test]
fn duplicate_explicit_impl_is_t250() {
    let defs = "record Point { x: i64, y: i64 }\n\
        impl Hash for Point { fn hash(self: Point) -> i64 { return self.x; } }\n\
        impl Hash for Point { fn hash(self: Point) -> i64 { return self.y; } }";
    assert!(
        fails_with(defs, "    return 0 - 1;", "T250"),
        "two impls of the same (trait, type) pair must be T250"
    );
}

// ── an explicit impl of an undeclared trait ──────────────────────────────────

#[test]
fn explicit_impl_of_unknown_trait_is_t248() {
    let defs = "record Point { x: i64, y: i64 }\n\
        impl Bogus for Point { fn bogus(self: Point) -> i64 { return self.x; } }";
    assert!(
        fails_with(defs, "    return 0 - 1;", "T248"),
        "an explicit impl of an undeclared trait must be T248"
    );
}
