//! Step-0 de-risk spike for the `Map<str, V>` epic.
//!
//! Proves the exact nested-generic surface the map rests on: a GENERIC record
//! holding a `Vec<own-type-param>`, exercised through push / get / `set` /
//! `Option<V>` at **V=i64 AND V=i32**. Recon said this combo monomorphizes but
//! the precise "generic record holding `Vec<its-own-param>`" case was untested;
//! this is the value-checked proof (plan CF-8/NC-8 — not a compile-only pass).
//!
//! `Box<V>` is bare source: `Vec` / `Vec::` / `Option<` / `Some` / `None`
//! triggers pull `vec.sigil` + `option.sigil` in via ambient injection, exactly
//! as `Map<str, V>` will.
//!
//! Originally a `#[ignore]`d STOP gate (it caught two real type-checker gaps —
//! T150 on `Vec::new()` in a generic field, T049 on `None` in `-> Option<V>`);
//! both are now fixed by the generic-construction-inference PR (Fix A + Fix B in
//! `type_check/expressions.rs`), so this is a permanent green regression test for
//! the nested-generic surface every generic collection depends on.

mod common;

/// Compile + run a tool ending in `return 0 - <value>;`, recovering `<value>`.
use common::run_returning_negative;

// A generic record whose ONLY field is a `Vec` of its own type parameter, plus
// an impl that pushes/gets/sets `V` and returns `Option<V>`. The `make()` assoc
// fn mirrors `Map::new()` constructing a record with Vec fields; `find`
// mirrors `Map::get` returning `Option<V>`.
const BOX: &str = "\
record Box<V> { items: Vec<V> }\n\
impl Box<V> {\n\
\x20   pub fn make() -> Box<V> { return Box { items: Vec::new() }; }\n\
\x20   pub fn add(self: Box<V> @Mut, v: V) -> i64 ! { Alloc } { return self.items.push(v); }\n\
\x20   pub fn at(self: Box<V>, i: i64) -> V { return self.items.get(i); }\n\
\x20   pub fn put(self: Box<V> @Mut, i: i64, v: V) -> i64 { return self.items.set(i, v); }\n\
\x20   pub fn find(self: Box<V>, i: i64) -> Option<V> {\n\
\x20       if i < self.items.len() { return Some(self.items.get(i)); } else { return None; }\n\
\x20   }\n\
}";

fn tool(body: &str) -> String {
    format!(
        "module tool;\n{BOX}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

#[test]
fn nested_generic_box_i64_all_surfaces() {
    // V=i64: push two, set index 0, read both, Option Some/None via find.
    let src = tool(
        "    let b: Box<i64> = Box::make();\n\
         \x20   let p: i64 = b.add(100);\n\
         \x20   let q: i64 = b.add(200);\n\
         \x20   b.put(0, 999);\n\
         \x20   let v0: i64 = b.at(0);\n\
         \x20   let v1: i64 = b.at(1);\n\
         \x20   let found: Option<i64> = b.find(1);\n\
         \x20   let some_v: i64 = found.unwrap_or(0);\n\
         \x20   let missing: Option<i64> = b.find(5);\n\
         \x20   let none_v: i64 = missing.unwrap_or(42);\n\
         \x20   return 0 - (v0 + v1 + some_v + none_v);",
    );
    // set→get v0=999, push→get v1=200, Some(200)→200, None→42 = 1441.
    assert_eq!(run_returning_negative(&src), 1441);
}

#[test]
fn nested_generic_box_i32_all_surfaces() {
    // V=i32: literal args narrow to i32 at the call site (#132). Values checked
    // via comparison branches (i32 get can't sum with the i64 sentinel); each
    // failure sentinel 1..4 pinpoints the broken surface, 88 = all pass.
    let src = tool(
        "    let b: Box<i32> = Box::make();\n\
         \x20   let p: i64 = b.add(1000000);\n\
         \x20   let q: i64 = b.add(7);\n\
         \x20   b.put(0, 999);\n\
         \x20   let v0: i32 = b.at(0);\n\
         \x20   let v1: i32 = b.at(1);\n\
         \x20   let found: Option<i32> = b.find(1);\n\
         \x20   let some_v: i32 = found.unwrap_or(0);\n\
         \x20   let missing: Option<i32> = b.find(5);\n\
         \x20   let none_v: i32 = missing.unwrap_or(42);\n\
         \x20   if v0 == 999 {\n\
         \x20       if v1 == 7 {\n\
         \x20           if some_v == 7 {\n\
         \x20               if none_v == 42 {\n\
         \x20                   return 0 - 88;\n\
         \x20               } else { return 0 - 4; }\n\
         \x20           } else { return 0 - 3; }\n\
         \x20       } else { return 0 - 2; }\n\
         \x20   } else { return 0 - 1; }",
    );
    // set→get v0=999, push→get v1=7, Some(7)→7, None→42 → all pass → 88.
    assert_eq!(run_returning_negative(&src), 88);
}
