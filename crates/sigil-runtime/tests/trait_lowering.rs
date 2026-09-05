//! PR-3c of the trait epic — primitive `.hash()`/`.eq()` LOWERING, end to end.
//!
//! `(str|i64|bool).hash()` / `.eq(o)` desugar to the `traits` module's built-in
//! impl fns, and `traits.sigil` is ambient-injected by a `.hash(`/`.eq(` call or
//! a `: Hash`/`: Eq` bound — so NONE of these programs declare the traits or
//! import anything. This closes the heart: a bounded generic whose body calls the
//! trait method lowers to real wasm.
//!
//! Notably `str.eq` does BYTE equality, including on a `substr` VIEW — the thing
//! the `==` operator cannot do (it compares only the fat-pointer address; the
//! lexer-spike gap). Values are recovered via the negative-sentinel convention.

mod common;

use common::run_returning_negative as run_neg;

fn djb2(s: &str) -> i64 {
    let mut h: i64 = 5381;
    for b in s.bytes() {
        h = (h << 5).wrapping_add(h).wrapping_add(b as i64);
    }
    h
}

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn tool_with_defs(defs: &str, body: &str) -> String {
    format!(
        "module tool;\n{defs}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

// ── direct primitive .hash() lowers (ambient-injected, no decls) ─────────────

#[test]
fn str_hash_lowers() {
    let r = run_neg(&tool("    let s: str = \"hi\";\n    return 0 - s.hash();"));
    assert_eq!(r, djb2("hi"));
}

#[test]
fn i64_hash_is_identity() {
    let r = run_neg(&tool("    let x: i64 = 42;\n    return 0 - x.hash();"));
    assert_eq!(r, 42);
}

#[test]
fn bool_hash_is_one_or_zero() {
    let t = run_neg(&tool("    let b: bool = true;\n    return 0 - b.hash();"));
    assert_eq!(t, 1);
    // false hashes to 0 → `0 - 0` is not negative, so encode via +5.
    let f = run_neg(&tool(
        "    let b: bool = false;\n    return 0 - (b.hash() + 5);",
    ));
    assert_eq!(f, 5);
}

// ── str.eq is BYTE equality — works on a substr VIEW (`==` cannot) ───────────

#[test]
fn str_eq_is_byte_equality_on_a_view() {
    // v is a substr view "fn"; `v.eq("fn")` is true by BYTES, where `v == "fn"`
    // would be false (different data pointers — the lexer-spike gap).
    let body = "    let s: str = \"fnx\";\n\
        \x20   let v: str = s.substr(0, 2);\n\
        \x20   if v.eq(\"fn\") {\n\
        \x20       return 0 - 11;\n\
        \x20   } else {\n\
        \x20       return 0 - 22;\n\
        \x20   }";
    assert_eq!(run_neg(&tool(body)), 11);
}

#[test]
fn str_eq_distinguishes_different_strings() {
    let body = "    let a: str = \"hi\";\n\
        \x20   let b: str = \"ho\";\n\
        \x20   if a.eq(b) {\n\
        \x20       return 0 - 1;\n\
        \x20   } else {\n\
        \x20       return 0 - 2;\n\
        \x20   }";
    assert_eq!(run_neg(&tool(body)), 2);
}

// ── the headline: a bounded generic's body calls the trait method ────────────

#[test]
fn generic_keyed_str_lowers_through_the_bound() {
    // `<T: Hash>` ambient-injects `traits` (declaring Hash + str_hash); the body's
    // `k.hash()` (k: str after mono) lowers to `traits::str_hash`. No inline decls.
    let src = tool_with_defs(
        "fn keyed<T: Hash>(k: T) -> i64 { return k.hash(); }",
        "    let s: str = \"hi\";\n    let r: i64 = keyed(s);\n    return 0 - r;",
    );
    assert_eq!(run_neg(&src), djb2("hi"));
}

#[test]
fn generic_keyed_i64_lowers_through_the_bound() {
    let src = tool_with_defs(
        "fn keyed<T: Hash>(k: T) -> i64 { return k.hash(); }",
        "    let n: i64 = 42;\n    let r: i64 = keyed(n);\n    return 0 - r;",
    );
    assert_eq!(run_neg(&src), 42);
}

#[test]
fn composed_bound_keyed_lowers() {
    // `<K: Hash + Eq>` — both bounds satisfied by str; the body uses the Hash half.
    let src = tool_with_defs(
        "fn keyed<K: Hash + Eq>(k: K) -> i64 { return k.hash(); }",
        "    let s: str = \"hi\";\n    let r: i64 = keyed(s);\n    return 0 - r;",
    );
    assert_eq!(run_neg(&src), djb2("hi"));
}

// ── direct == oracle agreement: str.hash matches the map's DJB2 (CM-T6) ───────

#[test]
fn str_hash_matches_djb2_for_several_inputs() {
    for s in ["a", "ab", "key", "value"] {
        let body = format!("    let s: str = \"{s}\";\n    return 0 - s.hash();");
        assert_eq!(
            run_neg(&tool(&body)),
            djb2(s),
            "str_hash mismatch for {s:?}"
        );
    }
}
