//! Adversarial stress suite for the merged `Map<str, V>` (post-PR-4).
//!
//! These tests try to BREAK the map end-to-end through the ambient/cross-module
//! path (a bare `Map`, no inline `module map;`) — the exact surface user code
//! hits. The focus is the corruptions that a naive `len()`-based suite would
//! MISS: a mis-homed dense-value index (`vidx`) after a rehash, a probe chain
//! that never resolves, an absent key landing on an occupied home slot, an
//! overwrite that secretly double-appends, a negative DJB2 hash that a `%` would
//! send out of range, a stale array alias across a grow, and cross-map clobber.
//!
//! Key generation is the binding constraint: SIGIL has no `itoa`/concat, so a
//! `str` cannot be BUILT from a loop counter at runtime — every key is a literal.
//! The distinct-key-at-scale scenarios therefore HOST-GENERATE the SIGIL source
//! (the Rust loop emits N literal `insert`/`get_or` statements), while the
//! value/aliasing mechanics stay in-SIGIL. Values are distinct and non-linear
//! (`7*i + 3`) so any mis-mapping — a dropped key, a swapped `vidx`, a stale
//! cached hash — changes the checksum.
//!
//! `str_hash` is DJB2 (`h = (h<<5) + h + b`, wrapping i64, seed 5381) over the
//! key's bytes; `djb2` below mirrors it EXACTLY so collisions/negative hashes can
//! be host-computed and the home slot (`hash & (slots-1)`) predicted.
//!
//! Convention: a tool returns `0 - <value>` (a negative i64) which the runtime
//! surfaces as `Trapped { "tool returned error (N)" }`; `neg`/`run_neg` recover
//! `N`. A genuine bug surfaces either as a different `N` (wrong value) or a
//! non-trap error (the module failed to validate / a real OOB trap).

mod common;

use std::collections::HashMap;

/// Wrap a `tool_main` body (bare `Map` — ambient injection supplies map.sigil
/// + its transitive vec/option/result/traits).
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// Wrap with extra top-level definitions (e.g. a record holding a Map).
fn tool_with_defs(defs: &str, body: &str) -> String {
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

use common::run_returning_negative as run_neg;

fn neg(body: &str) -> i64 {
    run_neg(&tool(body))
}

/// The value stored for the i-th distinct key: distinct AND non-linear so a
/// swapped/dropped entry always changes the checksum. Never 0 (so an absent key
/// read with default 0 is detectable).
fn val(i: i64) -> i64 {
    7 * i + 3
}

// ── host mirror of str_hash (DJB2) ────────────────────────────────────────

/// Byte-for-byte mirror of `stdlib/sigil/traits.sigil`'s `str_hash`: seed 5381,
/// `h = (h<<5) + h + b` over each key byte, wrapping in i64 (matching wasm's
/// wrapping i64 shl/add). ASCII keys only ⇒ `byte_at` == the raw byte.
fn djb2(key: &str) -> i64 {
    let mut h: i64 = 5381;
    for &byte in key.as_bytes() {
        let b = byte as i64; // 0..=255, exactly what byte_at yields
        h = h.wrapping_shl(5).wrapping_add(h).wrapping_add(b);
    }
    h
}

/// Home slot for a power-of-two `slots`, exactly as the map computes it
/// (`hash & (slots - 1)` — sign-agnostic, always in `[0, slots)`).
fn home(key: &str, slots: i64) -> i64 {
    djb2(key) & (slots - 1)
}

/// Find `count` distinct keys that all share ONE home slot at `slots`, plus one
/// EXTRA key with that same home (an absent-probe that must traverse the full
/// occupied chain to an EMPTY slot). Deterministic: keys are generated in a
/// fixed order and the first home value to accumulate `count + 1` wins.
fn colliding_keys(slots: i64, count: usize) -> (Vec<String>, String) {
    let mut buckets: HashMap<i64, Vec<String>> = HashMap::new();
    let mut i: u64 = 0;
    loop {
        let key = format!("c{i}");
        let h = home(&key, slots);
        let bucket = buckets.entry(h).or_default();
        bucket.push(key);
        if bucket.len() > count {
            let mut keys = buckets.remove(&h).expect("just inserted");
            let absent = keys.pop().expect("count + 1 present");
            keys.truncate(count);
            return (keys, absent);
        }
        i += 1;
        assert!(
            i < 5_000_000,
            "no {count}-way collision found at slots {slots}"
        );
    }
}

// ── deep insert: every value survives many rehashes ──────────────────────────

#[test]
fn deep_insert_reads_every_value_across_many_grows() {
    // N distinct literal keys from a LAZY map (slots 8) ⇒ ~6 doublings
    // (8→16→32→64→128→256→512). Read EVERY value back and checksum. A reordered
    // / under-copied / wrong-cached-hash rehash, or a stale `vidx`, drops or
    // swaps a value and changes the sum. Non-linear values defeat symmetric
    // (order-reversing) corruptions. `len` is folded in to pin the live count.
    const N: i64 = 256;
    let mut body = String::from("    let m: Map<str, i64> = Map::new();\n");
    for i in 0..N {
        body.push_str(&format!("    m.insert(\"k{i}\", {});\n", val(i)));
    }
    body.push_str("    let mut s: i64 = 0;\n");
    for i in 0..N {
        body.push_str(&format!("    s = s + m.get_or(\"k{i}\", 0);\n"));
    }
    body.push_str("    return 0 - (s + m.len());");
    let expected: i64 = (0..N).map(val).sum::<i64>() + N;
    assert_eq!(neg(&body), expected);
}

// ── collision chain: long probe + key_eq disambiguation ──────────────────────

#[test]
fn high_collision_chain_resolves_every_value() {
    // `with_capacity(40)` pins slots = 64 (smallest pow2 with cap*7 > 400). All
    // 24 keys share ONE home slot, so every read probes a 24-long chain and
    // relies on `key_eq` to pick the right entry. 24 < 0.7*64 ⇒ no grow, so the
    // collision assumption (slots == 64) holds; `capacity()` is folded into the
    // checksum so any drift in `with_capacity`'s sizing fails LOUDLY rather than
    // silently scattering the keys.
    const K: usize = 24;
    let (keys, _absent) = colliding_keys(64, K);
    let mut body = String::from("    let m: Map<str, i64> = Map::with_capacity(40);\n");
    for (i, k) in keys.iter().enumerate() {
        body.push_str(&format!("    m.insert(\"{k}\", {});\n", val(i as i64)));
    }
    body.push_str("    let mut s: i64 = 0;\n");
    for k in &keys {
        body.push_str(&format!("    s = s + m.get_or(\"{k}\", 0);\n"));
    }
    body.push_str("    return 0 - (s + m.capacity());");
    let expected: i64 = (0..K as i64).map(val).sum::<i64>() + 64;
    assert_eq!(neg(&body), expected);
}

#[test]
fn absent_key_on_occupied_home_slot_returns_default() {
    // The deadliest miss-read: an ABSENT key whose home slot is the head of a
    // fully-occupied probe chain must walk the chain to an EMPTY slot and return
    // the DEFAULT — never a neighbor's value. Uses the same pinned slots = 64 and
    // the extra collider from `colliding_keys` (guaranteed same home, guaranteed
    // not inserted).
    const K: usize = 16;
    let (keys, absent) = colliding_keys(64, K);
    assert_eq!(
        home(&absent, 64),
        home(&keys[0], 64),
        "absent probe must share the chain's home slot"
    );
    let mut body = String::from("    let m: Map<str, i64> = Map::with_capacity(40);\n");
    for (i, k) in keys.iter().enumerate() {
        body.push_str(&format!("    m.insert(\"{k}\", {});\n", val(i as i64)));
    }
    // Default sentinel 99_999 is distinct from every val(i) (= 7i+3 ≤ 108).
    body.push_str(&format!("    return 0 - m.get_or(\"{absent}\", 99999);"));
    assert_eq!(neg(&body), 99_999);
}

#[test]
fn negative_hash_key_round_trips() {
    // I2 / CF-D5 behaviorally: a key whose DJB2 is NEGATIVE (top bit set). The
    // home slot is `hash & (slots-1)` — sign-agnostic, always in range. A `%`
    // (forbidden, grep-gated) would give a negative remainder → OOB trap / wrong
    // slot. DJB2 only overflows i64 past ~13 bytes (33^13 > 2^63), so SHORT keys
    // are always positive — use a long padded key and host-pick the first whose
    // hash is negative (this is also the ONLY coverage of the negative-hash path;
    // the short `k{i}` keys elsewhere never reach it).
    let key = (0..100_000)
        .map(|i| format!("neg_hash_probe_{i}"))
        .find(|k| djb2(k) < 0)
        .expect("a long key yields a negative DJB2");
    let body = format!(
        "    let m: Map<str, i64> = Map::new();\n    m.insert(\"{key}\", 4242);\n    return 0 - m.get_or(\"{key}\", 0);"
    );
    assert_eq!(neg(&body), 4242);
}

// ── reference semantics: growth during aliasing ──────────────────────────────

#[test]
fn growth_during_aliasing_repoints_all_holders() {
    // THE subtle one. `a` and `b` alias one heap header. Inserting distinct keys
    // through `b` past the 0.7 load triggers a grow that REASSIGNS the five slot
    // arrays (and maybe the arena) on the SHARED header. `a` must observe the new
    // arrays — a stale-array alias would read the orphaned (smaller) arrays and
    // return garbage or trap. with_capacity(2) → slots 8; 6 inserts force a grow.
    let mut body = String::from(
        "    let a: Map<str, i64> = Map::with_capacity(2);\n    let b: Map<str, i64> = a;\n",
    );
    for i in 0..6 {
        body.push_str(&format!("    b.insert(\"g{i}\", {});\n", 100 + i));
    }
    body.push_str("    return 0 - (a.get_or(\"g0\", 0) + a.get_or(\"g5\", 0) + a.len());");
    // 100 + 105 + len 6 = 211, all observed through the aliasing binding `a`.
    assert_eq!(neg(&body), 211);
}

// ── non-interference: two maps growing interleaved ───────────────────────────

#[test]
fn two_maps_growing_interleaved_do_not_corrupt() {
    // Two independent maps, inserts interleaved so their reallocations straddle
    // each other; each must keep its own arrays + arena. 12 keys each ⇒ each
    // grows twice (8→16→32). Read EVERY value from BOTH back.
    const E: i64 = 12;
    let mut body = String::from(
        "    let a: Map<str, i64> = Map::new();\n    let b: Map<str, i64> = Map::new();\n",
    );
    for i in 0..E {
        body.push_str(&format!("    a.insert(\"a{i}\", {});\n", val(i)));
        body.push_str(&format!("    b.insert(\"b{i}\", {});\n", val(i) + 1));
    }
    body.push_str("    let mut s: i64 = 0;\n");
    for i in 0..E {
        body.push_str(&format!(
            "    s = s + a.get_or(\"a{i}\", 0) + b.get_or(\"b{i}\", 0);\n"
        ));
    }
    body.push_str("    return 0 - s;");
    // Σ a-values + Σ b-values = Σ val(i) + Σ (val(i)+1) = 2·Σ val(i) + E.
    let expected: i64 = 2 * (0..E).map(val).sum::<i64>() + E;
    assert_eq!(neg(&body), expected);
}

// ── overwrite: no double-append, no double-count, no spurious grow ───────────

#[test]
fn overwrite_same_key_pins_len_and_capacity() {
    // CF-D4 / CF-D6 behaviorally: overwriting ONE key 50 times must update the
    // value in place — never append to the arena, never push `vals`, never bump
    // `count`, never grow. Pins value==last, len==1, AND capacity==8 (the lazy
    // first size). A double-append/double-count bug perturbs len or capacity.
    let mut body = String::from("    let m: Map<str, i64> = Map::new();\n");
    for v in 1..=50 {
        body.push_str(&format!("    m.insert(\"k\", {v});\n"));
    }
    body.push_str("    return 0 - (m.get_or(\"k\", 0) * 1000 + m.len() * 10 + m.capacity());");
    // value 50 (last) ·1000 + len 1 ·10 + capacity 8 = 50_018.
    assert_eq!(neg(&body), 50_018);
}

// ── key compare is length-first: nested prefixes must not alias ───────────────

#[test]
fn nested_prefix_keys_do_not_alias() {
    // I4: `key_eq` compares LENGTH before the byte loop, so `"p"`, `"pp"`,
    // `"ppp"`, … (each a prefix of the next) are all distinct. A byte-loop-only
    // compare would alias a key with any of its extensions. 20 nested prefixes,
    // distinct values, full checksum.
    const P: i64 = 20;
    let key = |n: i64| "p".repeat(n as usize);
    let mut body = String::from("    let m: Map<str, i64> = Map::new();\n");
    for i in 1..=P {
        body.push_str(&format!("    m.insert(\"{}\", {});\n", key(i), val(i)));
    }
    body.push_str("    let mut s: i64 = 0;\n");
    for i in 1..=P {
        body.push_str(&format!("    s = s + m.get_or(\"{}\", 0);\n", key(i)));
    }
    body.push_str("    return 0 - s;");
    let expected: i64 = (1..=P).map(val).sum();
    assert_eq!(neg(&body), expected);
}

// ── present-0 vs absent, at scale (Option path) ──────────────────────────────

#[test]
fn present_zero_vs_absent_at_scale() {
    // I7 / CF-D6 after several grows: a key whose value is 0 reads as `Some(0)`,
    // an absent key as `None` — never confused with a value sentinel. Insert 50
    // keys (forcing grows) including `"zero" → 0`, then probe via `get`.
    let mut body = String::from("    let m: Map<str, i64> = Map::new();\n");
    for i in 0..50 {
        body.push_str(&format!("    m.insert(\"k{i}\", {});\n", val(i)));
    }
    body.push_str("    m.insert(\"zero\", 0);\n");
    body.push_str("    let pz: Option<i64> = m.get(\"zero\");\n");
    body.push_str("    let ab: Option<i64> = m.get(\"ghost\");\n");
    body.push_str("    return 0 - (pz.unwrap_or(0 - 1) + 100 + ab.unwrap_or(5) + 1000);");
    // present zero → Some(0) → 0; absent ghost → None → 5. 0 + 100 + 5 + 1000 = 1105.
    assert_eq!(neg(&body), 1105);
}

// ── Map stored in a record field ──────────────────────────────────────────

#[test]
fn map_as_record_field() {
    // A user record holds a Map; method dispatch on a field-access receiver
    // (`h.m.insert(..)`) must mutate the shared header. let-first idiom supplies
    // the field annotation (the assoc-fn-in-field-position boundary, AG-C2).
    let src = tool_with_defs(
        "record Holder { m: Map<str, i64> }",
        "    let mm: Map<str, i64> = Map::new();\n\
         \x20   let h: Holder = Holder { m: mm };\n\
         \x20   h.m.insert(\"x\", 3);\n\
         \x20   h.m.insert(\"y\", 4);\n\
         \x20   return 0 - (h.m.len() + h.m.get_or(\"y\", 0));",
    );
    assert_eq!(run_neg(&src), 6); // len 2 + get_or("y") 4
}
