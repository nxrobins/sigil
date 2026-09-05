//! PR-7 — the trait Wall's adversarial stress capstone.
//!
//! The unit suites (`trait_lowering` / `trait_structural` / `trait_explicit_impl`)
//! prove each PIECE of the trait machinery in isolation, and `map_stress.rs`
//! hammers the `Map<str, V>` instance. This file is the INTEGRATION wall: the
//! whole stack — generic bounds, all three satisfaction sources, and the real
//! open-addressing `Map<K: Hash + Eq, V>` — exercised together at SCALE, across
//! the dimensions `map_stress` cannot reach because it is `str`-keyed:
//!
//!   * `Map<i64, V>` at scale — IDENTITY hash, deep insert across grows, a
//!     pinned-`slots` collision chain (keys sharing a home residue), and a
//!     NEGATIVE i64 key (the `& (slots-1)` sign-agnosticism applied to the key
//!     itself, not just a hashed `str`).
//!   * `Map<Point, V>` at scale — a USER RECORD key satisfying `Hash + Eq`
//!     STRUCTURALLY, driven through the full probe/grow machinery, plus a
//!     same-`hash` collision set that ONLY `eq` (comparing both fields) can
//!     disambiguate.
//!   * the same via an EXPLICIT `impl Hash for Point` / `impl Eq for Point`
//!     (the explicit-impl → map-key path, end to end).
//!   * COMPOSITION — `Map<str, Vec<i64>>` (the trait map holding the generic
//!     collection as its VALUE: `vals` is a `Vec<Vec<i64>>`).
//!   * adversarial REJECTION in map position — a key type missing `eq` is
//!     refused (no `Map<BadKey, V>` reaches codegen), and an orphan
//!     `impl Hash for i64` in a map-using program is still T249.
//!
//! Convention (mirrors `map_stress`): a tool returns `0 - <value>` (a negative
//! i64) surfaced as `Trapped { "tool returned error (N)" }`; `run_neg`/`neg`
//! recover `N`. A genuine bug surfaces as a different `N` (wrong value) or a
//! non-trap error (the module failed to validate / a real OOB trap).

mod common;

use sigil_compiler::compile_tool;

use common::run_returning_negative as run_neg;

/// Wrap a bare-`Map` `tool_main` body — ambient injection supplies map.sigil +
/// its transitive vec/option/result/traits.
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// Wrap with extra top-level definitions (a key record + its impls).
fn tool_with_defs(defs: &str, body: &str) -> String {
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    run_neg(&tool(body))
}

fn neg_defs(defs: &str, body: &str) -> i64 {
    run_neg(&tool_with_defs(defs, body))
}

/// True iff the program FAILS to compile with a diagnostic carrying `code`.
fn fails_with(defs: &str, body: &str, code: &str) -> bool {
    match compile_tool(&tool_with_defs(defs, body)) {
        Ok(_) => false,
        Err(e) => format!("{e:?}").contains(code),
    }
}

/// Distinct, non-linear value for the i-th key (never 0, so an absent read with
/// default 0 is detectable; non-linear so a swap/drop always perturbs the sum).
fn val(i: i64) -> i64 {
    7 * i + 3
}

/// A structural `Point` key: `hash` is `x` ALONE (so equal-`x` points collide on
/// their home slot), `eq` compares BOTH fields (so the probe chain disambiguates
/// them). Shared by the structural-satisfaction tests.
const POINT_STRUCTURAL: &str = "\
record Point { x: i64, y: i64 }\n\
impl Point {\n\
    fn hash(self: Point) -> i64 { return self.x; }\n\
    fn eq(self: Point, other: Point) -> bool {\n\
        if self.x == other.x {\n\
            return self.y == other.y;\n\
        } else {\n\
            return false;\n\
        }\n\
    }\n\
}";

// ── Map<i64, V>: identity hash, deep insert across many grows ─────────────────

#[test]
fn i64_keyed_deep_insert_survives_grows() {
    // N distinct i64 keys (1000+i) from a LAZY map (slots 8) ⇒ ~6 doublings.
    // i64 hash is identity, so home == key & (slots-1). Keys are bound to a
    // reused i64 local (a bare integer literal through a generic param does not
    // concretize — #132 — but assigning a literal to a typed local does). Read
    // EVERY value back + fold `len`: a dropped/swapped/mis-rehomed entry changes
    // the checksum.
    const N: i64 = 256;
    let mut body =
        String::from("    let m: Map<i64, i64> = Map::new();\n    let mut k: i64 = 0;\n");
    for i in 0..N {
        body.push_str(&format!(
            "    k = {};\n    m.insert(k, {});\n",
            1000 + i,
            val(i)
        ));
    }
    body.push_str("    let mut s: i64 = 0;\n");
    for i in 0..N {
        body.push_str(&format!(
            "    k = {};\n    s = s + m.get_or(k, 0);\n",
            1000 + i
        ));
    }
    body.push_str("    return 0 - (s + m.len());");
    let expected: i64 = (0..N).map(val).sum::<i64>() + N;
    assert_eq!(neg(&body), expected);
}

#[test]
fn i64_keyed_collision_chain_resolves_every_value() {
    // `with_capacity(40)` pins slots = 64. Keys 5, 69, 133, … (5 + 64·j) all share
    // home slot `5` (identity hash & 63 == 5), so every read probes a long chain
    // and relies on `eq` (native i64 ==) to pick the right entry. 24 < 0.7·64 ⇒ no
    // grow; `capacity()` is folded in so any sizing drift fails LOUDLY.
    const K: i64 = 24;
    let mut body = String::from(
        "    let m: Map<i64, i64> = Map::with_capacity(40);\n    let mut k: i64 = 0;\n",
    );
    for j in 0..K {
        body.push_str(&format!(
            "    k = {};\n    m.insert(k, {});\n",
            5 + 64 * j,
            val(j)
        ));
    }
    body.push_str("    let mut s: i64 = 0;\n");
    for j in 0..K {
        body.push_str(&format!(
            "    k = {};\n    s = s + m.get_or(k, 0);\n",
            5 + 64 * j
        ));
    }
    body.push_str("    return 0 - (s + m.capacity());");
    let expected: i64 = (0..K).map(val).sum::<i64>() + 64;
    assert_eq!(neg(&body), expected);
}

#[test]
fn negative_i64_key_round_trips() {
    // CF-D5 on the KEY itself: a negative i64 key (identity hash is negative). The
    // home slot is `hash & (slots-1)` — sign-agnostic, always in `[0, slots)`. A
    // `%` (forbidden, grep-gated) would give a negative remainder → OOB / wrong
    // slot. `0 - 7` keeps it i64 (a bare `-7` literal arg would not concretize).
    let body = "    let m: Map<i64, i64> = Map::new();\n\
        \x20   let k: i64 = 0 - 7;\n\
        \x20   m.insert(k, 4242);\n\
        \x20   return 0 - m.get_or(k, 0);";
    assert_eq!(neg(body), 4242);
}

// ── Map<Point, V>: a user record key, satisfied STRUCTURALLY ──────────────────

#[test]
fn record_keyed_deep_insert_survives_grows() {
    // The headline: a USER RECORD as a `Map` key, satisfying `Hash + Eq`
    // structurally (no `impl Trait`), driven through the FULL open-addressing
    // map at scale. `Point { i, i }` for i in 0..N — distinct keys, identity-ish
    // `hash = x` spreads the homes. A single reused mutable `p` rebinds to a fresh
    // heap Point each iteration; `insert` captures that pointer, so the map holds
    // N distinct keys. Reads reconstruct `Point { i, i }` — `eq` (both fields)
    // matches the stored key by VALUE.
    const N: i64 = 128;
    let mut body = String::from(
        "    let m: Map<Point, i64> = Map::new();\n    let mut p: Point = Point { x: 0, y: 0 };\n",
    );
    for i in 0..N {
        body.push_str(&format!(
            "    p = Point {{ x: {i}, y: {i} }};\n    m.insert(p, {});\n",
            val(i)
        ));
    }
    body.push_str("    let mut s: i64 = 0;\n");
    for i in 0..N {
        body.push_str(&format!(
            "    p = Point {{ x: {i}, y: {i} }};\n    s = s + m.get_or(p, 0);\n"
        ));
    }
    body.push_str("    return 0 - (s + m.len());");
    let expected: i64 = (0..N).map(val).sum::<i64>() + N;
    assert_eq!(neg_defs(POINT_STRUCTURAL, &body), expected);
}

#[test]
fn record_keyed_hash_collision_resolved_by_eq() {
    // The record analog of a full collision chain: K points ALL with `x == 7`
    // (so `hash == 7` for every one ⇒ one shared home slot) but DISTINCT `y`. The
    // probe chain can only be walked correctly if `eq` compares BOTH fields — a
    // hash-only or x-only compare would alias them and return a neighbor's value.
    // `with_capacity(40)` pins slots 64 (K=20 < 0.7·64, no grow).
    const K: i64 = 20;
    let mut body = String::from(
        "    let m: Map<Point, i64> = Map::with_capacity(40);\n    let mut p: Point = Point { x: 7, y: 0 };\n",
    );
    for j in 0..K {
        body.push_str(&format!(
            "    p = Point {{ x: 7, y: {j} }};\n    m.insert(p, {});\n",
            val(j)
        ));
    }
    body.push_str("    let mut s: i64 = 0;\n");
    for j in 0..K {
        body.push_str(&format!(
            "    p = Point {{ x: 7, y: {j} }};\n    s = s + m.get_or(p, 0);\n"
        ));
    }
    body.push_str("    return 0 - (s + m.capacity());");
    let expected: i64 = (0..K).map(val).sum::<i64>() + 64;
    assert_eq!(neg_defs(POINT_STRUCTURAL, &body), expected);
}

// ── Map<Point, V>: the SAME, satisfied via EXPLICIT `impl Trait for Point` ─────

#[test]
fn record_keyed_via_explicit_impl_round_trips() {
    // `Point` satisfies `Hash + Eq` through EXPLICIT impls (not inherent methods).
    // The explicit-impl → map-key path end to end: the impls register Point::hash
    // / Point::eq exactly as inherent methods, so `Map<Point, i64>` monomorphizes
    // and round-trips. Three distinct points across a grow boundary.
    let defs = "record Point { x: i64, y: i64 }\n\
        impl Hash for Point { fn hash(self: Point) -> i64 { return self.x; } }\n\
        impl Eq for Point {\n\
            fn eq(self: Point, other: Point) -> bool {\n\
                if self.x == other.x {\n\
                    return self.y == other.y;\n\
                } else {\n\
                    return false;\n\
                }\n\
            }\n\
        }";
    let body = "    let m: Map<Point, i64> = Map::new();\n\
        \x20   let mut p: Point = Point { x: 0, y: 0 };\n\
        \x20   p = Point { x: 1, y: 1 };\n    m.insert(p, 10);\n\
        \x20   p = Point { x: 1, y: 2 };\n    m.insert(p, 20);\n\
        \x20   p = Point { x: 2, y: 1 };\n    m.insert(p, 40);\n\
        \x20   let mut s: i64 = 0;\n\
        \x20   p = Point { x: 1, y: 2 };\n    s = s + m.get_or(p, 0);\n\
        \x20   p = Point { x: 2, y: 1 };\n    s = s + m.get_or(p, 0);\n\
        \x20   return 0 - (s + m.len());";
    // get 20 + get 40 + len 3 = 63.
    assert_eq!(neg_defs(defs, body), 63);
}

// ── composition: the trait map holds the generic collection as its VALUE ───────

#[test]
fn map_of_vectors_composes() {
    // `Map<str, Vec<i64>>` — the map's `vals` field is a `Vec<Vec<i64>>` (nested
    // generic). Insert two vectors, read one back through `get -> Option<Vec<i64>>`
    // + `unwrap_or`, and index it. Exercises Map ∘ Vec ∘ Option in one value path.
    //
    // The trailing `> >` carries a SPACE: the lexer tokenizes a bare `>>` as one
    // shift operator, so a doubly-nested type-arg close (`Vec<i64>>`) is a P001
    // parse error today. The space splits it into two `>` — a known lexer quirk,
    // not a type-system limit (the composition itself monomorphizes fine).
    let body = "    let m: Map<str, Vec<i64> > = Map::new();\n\
        \x20   let a: Vec<i64> = Vec::new();\n\
        \x20   a.push(10);\n    a.push(20);\n    a.push(30);\n\
        \x20   m.insert(\"a\", a);\n\
        \x20   let b: Vec<i64> = Vec::new();\n\
        \x20   b.push(99);\n\
        \x20   m.insert(\"b\", b);\n\
        \x20   let g: Option<Vec<i64> > = m.get(\"a\");\n\
        \x20   let got: Vec<i64> = g.unwrap_or(Vec::new());\n\
        \x20   return 0 - (got.get(2) + got.len() + m.len());";
    // got = [10,20,30] ⇒ get(2)=30, len 3; m.len 2. 30 + 3 + 2 = 35.
    assert_eq!(neg(body), 35);
}

// ── adversarial rejection in MAP position ─────────────────────────────────────

#[test]
fn map_key_missing_eq_is_rejected() {
    // A `Bad` record provides `hash` but NOT `eq`, so it does not satisfy the
    // `Eq` half of `Map<K: Hash + Eq, V>`. The use IS refused — no `Map<Bad, V>`
    // monomorph reaches codegen — which is the load-bearing invariant.
    //
    // It is refused via T132 (`stored.eq(key)` can't resolve `eq` on `Bad`) deep
    // inside the monomorphized `insert`, NOT as a clean T245 at the `Map<Bad, _>`
    // construction: `check_bounds` is wired at the generic-fn instantiation site
    // but not yet at record construction (PR-6's documented deferred gap). This
    // test pins the CURRENT behavior; when bound-at-construction lands it flips to
    // a clean construction-site diagnostic and this expectation updates with it.
    let defs = "record Bad { x: i64 }\n\
        impl Bad { fn hash(self: Bad) -> i64 { return self.x; } }";
    let body = "    let m: Map<Bad, i64> = Map::new();\n\
        \x20   let b: Bad = Bad { x: 1 };\n\
        \x20   m.insert(b, 5);\n\
        \x20   return 0 - 1;";
    assert!(
        fails_with(defs, body, "T132"),
        "a Map key missing `eq` must be rejected (currently T132 deep in insert), never reach codegen"
    );
}

#[test]
fn orphan_impl_in_map_program_is_t249() {
    // The orphan rule is program-wide: an `impl Hash for i64` (a primitive, not a
    // declared record/enum — the built-in `i64: Hash` is unoverridable) is T249
    // even in a program that legitimately uses `Map<str, i64>` elsewhere. The
    // coherence check is not weakened by the map's presence.
    let defs = "impl Hash for i64 { fn hash(self: i64) -> i64 { return self; } }";
    let body = "    let m: Map<str, i64> = Map::new();\n\
        \x20   m.insert(\"x\", 1);\n\
        \x20   return 0 - m.len();";
    assert!(
        fails_with(defs, body, "T249"),
        "an orphan `impl Hash for i64` must be T249 even alongside Map use"
    );
}
