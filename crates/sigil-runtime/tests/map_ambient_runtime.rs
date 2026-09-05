//! Ambient-injection runtime test for `Map<str, V>` (PR 4).
//!
//! A BARE-`Map` tool — no inlined record/impl, no `module map;` — must
//! auto-inject `stdlib/sigil/map.sigil` AND its transitive deps (`vec.sigil`,
//! `option.sigil`, `result.sigil`, `traits.sigil`), then run end to end, exactly like
//! `Option`/`Vec`. The `Map::` / `Map<str, ` triggers do the pull; the value
//! must equal the same-module PR-3 result.

mod common;

use common::run_returning_negative;

#[test]
fn bare_map_auto_injects_and_runs() {
    // No `module map;`, no inline — just bare `Map`. `Map::new()` triggers
    // the pull of map.sigil + vec.sigil + option.sigil (transitive). Even though
    // the user code never writes `Some`/`None`/`Vec`, `map.sigil` needs them, so
    // the map-transitive injection supplies them.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let m: Map<str, i64> = Map::new();\n\
        \x20   let a: i64 = m.insert(\"key\", 42);\n\
        \x20   let b: i64 = m.insert(\"two\", 8);\n\
        \x20   return 0 - (m.get_or(\"key\", 0) + m.get_or(\"two\", 0) + m.len());\n\
        }\n";
    // 42 + 8 + len 2 = 52.
    assert_eq!(run_returning_negative(src), 52);
}

#[test]
fn bare_map_get_option_auto_injects() {
    // The `get -> Option<V>` path through ambient injection: `Option<i64>`
    // resolves because the map-transitive edge pulled `option.sigil`, and
    // `unwrap_or` runs.
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let m: Map<str, i64> = Map::new();\n\
        \x20   let a: i64 = m.insert(\"x\", 99);\n\
        \x20   let o: Option<i64> = m.get(\"x\");\n\
        \x20   return 0 - o.unwrap_or(0 - 1);\n\
        }\n";
    assert_eq!(run_returning_negative(src), 99);
}

#[test]
fn bare_map_growth_auto_injects() {
    // Growth across a rehash, bare-`Map` (CF-C6 parity: matches PR-3's
    // grow-preserves-all value of 81).
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
        \x20   let m: Map<str, i64> = Map::new();\n\
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
        \x20   return 0 - (sum + m.len() + m.capacity());\n\
        }\n";
    assert_eq!(run_returning_negative(src), 81);
}
