//! PR-6 verify-first spike — the generic `Map<K: Hash + Eq, V>` gate.
//!
//! Before rewriting the proven byte-arena `Map`, prove the headline payoff on
//! a FRESH minimal generic map: a `record Map<K: Hash + Eq, V>` whose methods
//! call `k.hash()` / `stored.eq(k)` on a generic key, monomorphized for THREE key
//! types — `str` (built-in impl), `i64` (built-in impl), and a user `record`
//! (structural). If this works, the registry pays off and PR-6's in-place rewrite
//! rests on solid ground. Nothing here is declared by hand: `Vec` / `traits`
//! ambient-inject off `Vec<` / the `: Hash` bound / the `.hash(` calls.
//!
//! The map is a linear table (keys/vals parallel `Vec`s) using `hash()` as a
//! fast-reject then `eq()` to confirm — enough to exercise both trait methods on
//! a generic param inside a generic record's method body.

mod common;

use common::run_returning_negative as run_neg;

/// The generic map definition, shared by every test.
const MAP: &str = "\
record Map<K: Hash + Eq, V> {\n\
    keys: Vec<K>,\n\
    vals: Vec<V>,\n\
}\n\
impl Map<K, V> {\n\
    fn insert(self: Map<K, V> @Mut, k: K, v: V) -> i64 ! { Alloc } {\n\
        let a: i64 = self.keys.push(k);\n\
        let b: i64 = self.vals.push(v);\n\
        return 0;\n\
    }\n\
    fn find(self: Map<K, V>, k: K) -> i64 {\n\
        let target: i64 = k.hash();\n\
        let n: i64 = self.keys.len();\n\
        let mut i: i64 = 0;\n\
        while i < n {\n\
            let stored = self.keys.get(i);\n\
            if stored.hash() == target {\n\
                if stored.eq(k) {\n\
                    return i;\n\
                } else {\n\
                }\n\
            } else {\n\
            }\n\
            i = i + 1;\n\
        }\n\
        return 0 - 1;\n\
    }\n\
}\n";

fn prog(extra_defs: &str, body: &str) -> String {
    format!(
        "module tool;\n{MAP}{extra_defs}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

#[test]
fn map_with_str_keys() {
    // Map<str, i64>: insert "a"→10, "b"→20; find "b" is at index 1.
    let body = "    let mut m: Map<str, i64> = Map { keys: Vec::new(), vals: Vec::new() };\n\
        \x20   let p: i64 = m.insert(\"a\", 10);\n\
        \x20   let q: i64 = m.insert(\"b\", 20);\n\
        \x20   return 0 - m.find(\"b\");";
    assert_eq!(run_neg(&prog("", body)), 1);
}

#[test]
fn map_with_i64_keys() {
    // Map<i64, str>: keys bound to locals so they concretize cleanly.
    let body = "    let mut m: Map<i64, str> = Map { keys: Vec::new(), vals: Vec::new() };\n\
        \x20   let k1: i64 = 10;\n\
        \x20   let k2: i64 = 20;\n\
        \x20   let p: i64 = m.insert(k1, \"x\");\n\
        \x20   let q: i64 = m.insert(k2, \"y\");\n\
        \x20   let probe: i64 = 20;\n\
        \x20   return 0 - m.find(probe);";
    assert_eq!(run_neg(&prog("", body)), 1);
}

#[test]
fn map_with_record_keys() {
    // Map<Point, i64> with a structural Point (hash = x, eq compares x). The
    // probe Point{2,9} matches the stored Point{2,2} by x.
    let point = "record Point { x: i64, y: i64 }\n\
        impl Point {\n\
        \x20   fn hash(self: Point) -> i64 { return self.x; }\n\
        \x20   fn eq(self: Point, other: Point) -> bool { return self.x == other.x; }\n\
        }";
    let body = "    let mut m: Map<Point, i64> = Map { keys: Vec::new(), vals: Vec::new() };\n\
        \x20   let a: Point = Point { x: 1, y: 1 };\n\
        \x20   let b: Point = Point { x: 2, y: 2 };\n\
        \x20   let p: i64 = m.insert(a, 100);\n\
        \x20   let q: i64 = m.insert(b, 200);\n\
        \x20   let probe: Point = Point { x: 2, y: 9 };\n\
        \x20   return 0 - m.find(probe);";
    assert_eq!(run_neg(&prog(point, body)), 1);
}

#[test]
fn map_miss_returns_negative_one() {
    // A key not present scans the whole table and returns -1 (encoded +5).
    let body = "    let mut m: Map<str, i64> = Map { keys: Vec::new(), vals: Vec::new() };\n\
        \x20   let p: i64 = m.insert(\"a\", 10);\n\
        \x20   let miss: i64 = m.find(\"zzz\");\n\
        \x20   return 0 - (miss + 5);";
    // -1 + 5 = 4.
    assert_eq!(run_neg(&prog("", body)), 4);
}
