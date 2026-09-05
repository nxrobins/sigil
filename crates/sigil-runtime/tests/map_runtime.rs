//! Runtime tests for the stdlib `Map<str, V>` (PR 3 — the live map).
//!
//! Each test concatenates the real `stdlib/sigil/map.sigil` (minus its own
//! `module map;` line) with a small `module tool` that uses it, compiles to
//! wasm, runs it, and reads the result back via the negative-sentinel
//! convention (a tool returning `0 - N` is recovered as `N`).

mod common;

const MAP: &str = include_str!("../../../stdlib/sigil/map.sigil");

use common::run_returning_negative;

/// Inline the real map.sigil into `module tool` (strip its `module map;` line)
/// so `Map` resolves same-module; `Vec`/`Option` arrive via ambient injection
/// (the `Vec::`/`Some`/`None` triggers in map.sigil's own body).
fn tool(body: &str) -> String {
    let defs = MAP.replace("\nmodule map;\n", "\n");
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// CF-D8 / verify-FIRST: a generic-impl method calling a SIBLING method on the
/// same `self` must monomorphize (`get` → `find_slot` is the pattern the whole
/// map rests on). The spike only proved a generic method calling `Vec`/`Option`
/// methods, not a sibling on `self`. If this fails, STOP — it's a monomorph gap
/// to surface, not build the map on.
#[test]
fn sibling_method_monomorphizes() {
    let src = "module tool;\n\
        record SibProbe<V> { x: i64 }\n\
        impl SibProbe<V> {\n\
        \x20   pub fn outer(self: SibProbe<V>) -> i64 { return self.inner() + 1; }\n\
        \x20   pub fn inner(self: SibProbe<V>) -> i64 { return self.x; }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let w: SibProbe<i64> = SibProbe { x: 41 };\n\
        \x20   return 0 - w.outer();\n\
        }\n";
    // outer() calls sibling inner() (== x == 41), + 1 = 42.
    assert_eq!(run_returning_negative(src), 42);
}

#[test]
fn insert_get_or_round_trip_i64() {
    // The core path: insert (ensure_buckets → arena_append → find_slot → push)
    // then read back via get_or (find_slot → key_eq), all monomorphized to i64.
    let src = tool(
        "    let m: Map<str, i64> = Map::new();\n\
         \x20   let a: i64 = m.insert(\"key\", 42);\n\
         \x20   return 0 - m.get_or(\"key\", 0 - 1);",
    );
    assert_eq!(run_returning_negative(&src), 42);
}

#[test]
fn insert_get_some_i64() {
    // The primary read: get returns Some(v) (generic Option construction, #150).
    let src = tool(
        "    let m: Map<str, i64> = Map::new();\n\
         \x20   let a: i64 = m.insert(\"key\", 42);\n\
         \x20   let o: Option<i64> = m.get(\"key\");\n\
         \x20   return 0 - o.unwrap_or(0 - 9);",
    );
    assert_eq!(run_returning_negative(&src), 42);
}

#[test]
fn get_absent_returns_default() {
    // An absent key on a non-empty map: find_slot lands on EMPTY → default.
    let src = tool(
        "    let m: Map<str, i64> = Map::new();\n\
         \x20   let a: i64 = m.insert(\"key\", 42);\n\
         \x20   return 0 - m.get_or(\"missing\", 77);",
    );
    assert_eq!(run_returning_negative(&src), 77);
}

#[test]
fn grow_preserves_all_entries() {
    // CF-D1: insert 10 distinct keys (cap 8 → grows to 16 at the 6th insert),
    // then read EVERY value back. A reorder / under-copy / wrong cached-hash in
    // grow would lose or corrupt an entry, changing the sum.
    let src = tool(
        "    let m: Map<str, i64> = Map::new();\n\
         \x20   let r1: i64 = m.insert(\"a\", 1);\n\
         \x20   let r2: i64 = m.insert(\"b\", 2);\n\
         \x20   let r3: i64 = m.insert(\"c\", 3);\n\
         \x20   let r4: i64 = m.insert(\"d\", 4);\n\
         \x20   let r5: i64 = m.insert(\"e\", 5);\n\
         \x20   let r6: i64 = m.insert(\"f\", 6);\n\
         \x20   let r7: i64 = m.insert(\"g\", 7);\n\
         \x20   let r8: i64 = m.insert(\"h\", 8);\n\
         \x20   let r9: i64 = m.insert(\"i\", 9);\n\
         \x20   let r10: i64 = m.insert(\"j\", 10);\n\
         \x20   let sum: i64 = m.get_or(\"a\", 0) + m.get_or(\"b\", 0) + m.get_or(\"c\", 0) + m.get_or(\"d\", 0) + m.get_or(\"e\", 0) + m.get_or(\"f\", 0) + m.get_or(\"g\", 0) + m.get_or(\"h\", 0) + m.get_or(\"i\", 0) + m.get_or(\"j\", 0);\n\
         \x20   return 0 - (sum + m.len() + m.capacity());",
    );
    // sum 1..10 = 55, len 10, capacity 16 (grew 8→16) → 55 + 10 + 16 = 81.
    assert_eq!(run_returning_negative(&src), 81);
}

#[test]
fn round_trip_i32() {
    // Generic at a SECOND width: Map<str, i32>. Literal values narrow to i32 at
    // the insert call (#132); checked via comparison branches.
    let src = tool(
        "    let m: Map<str, i32> = Map::new();\n\
         \x20   let a: i64 = m.insert(\"x\", 1000000);\n\
         \x20   let b: i64 = m.insert(\"y\", 7);\n\
         \x20   let vx: i32 = m.get_or(\"x\", 0);\n\
         \x20   let vy: i32 = m.get_or(\"y\", 0);\n\
         \x20   if vx == 1000000 {\n\
         \x20       if vy == 7 { return 0 - 55; } else { return 0 - 2; }\n\
         \x20   } else { return 0 - 1; }",
    );
    assert_eq!(run_returning_negative(&src), 55);
}

#[test]
fn overwrite_updates_value_not_count() {
    // CF-6: re-inserting a key overwrites the value in place; `len` is unchanged.
    let src = tool(
        "    let m: Map<str, i64> = Map::new();\n\
         \x20   let r1: i64 = m.insert(\"k\", 1);\n\
         \x20   let r2: i64 = m.insert(\"k\", 2);\n\
         \x20   return 0 - (m.get_or(\"k\", 0) * 100 + m.len());",
    );
    // overwrite → get_or 2, len 1 (unchanged) → 200 + 1 = 201.
    assert_eq!(run_returning_negative(&src), 201);
}

#[test]
fn present_zero_vs_absent() {
    // CF-7/I7: a present value of 0 reads as `Some(0)`; an absent key as `None`
    // — never confused.
    let src = tool(
        "    let m: Map<str, i64> = Map::new();\n\
         \x20   let r: i64 = m.insert(\"z\", 0);\n\
         \x20   let present: Option<i64> = m.get(\"z\");\n\
         \x20   let absent: Option<i64> = m.get(\"q\");\n\
         \x20   return 0 - (present.unwrap_or(0 - 1) + 100 + absent.unwrap_or(5) + 1000);",
    );
    // present z→0 → Some(0) → 0; absent q → None → 5. 0 + 100 + 5 + 1000 = 1105.
    assert_eq!(run_returning_negative(&src), 1105);
}

#[test]
fn length_first_key_compare() {
    // I4: "ab" and "abc" must not alias (length checked before the byte loop).
    let src = tool(
        "    let m: Map<str, i64> = Map::new();\n\
         \x20   let r1: i64 = m.insert(\"ab\", 11);\n\
         \x20   let r2: i64 = m.insert(\"abc\", 22);\n\
         \x20   return 0 - (m.get_or(\"ab\", 0) + m.get_or(\"abc\", 0) * 100);",
    );
    // ab→11, abc→22 → 11 + 2200 = 2211.
    assert_eq!(run_returning_negative(&src), 2211);
}

#[test]
fn contains_present_and_absent() {
    let src = tool(
        "    let m: Map<str, i64> = Map::new();\n\
         \x20   let r: i64 = m.insert(\"yes\", 1);\n\
         \x20   if m.contains(\"yes\") {\n\
         \x20       if m.contains(\"no\") { return 0 - 1; } else { return 0 - 9; }\n\
         \x20   } else { return 0 - 2; }",
    );
    // contains("yes") true, contains("no") false → 9.
    assert_eq!(run_returning_negative(&src), 9);
}
