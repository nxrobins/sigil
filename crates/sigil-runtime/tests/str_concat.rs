//! Owned-strings PR-2: `.concat()` — the first user-facing owned builder.
//!
//! `a.concat(b)` desugars (str-method dispatch) to `string::str_concat(a, b)` in
//! the ambient-injected `string.sigil`, which allocates `a.len()+b.len()` bytes,
//! copies `a` then `b`, and wraps via `str_from_raw`. These tests EXECUTE the
//! WASM and read the result back through `len`/`byte_at`/`substr` — so they also
//! prove `string.sigil` itself type-checks (default-frozen: the builder returns a
//! fresh str, never a frozen input → no T253) and that the `.concat(` ambient
//! trigger injects the owned module.
//!
//! NOTE (mirrors str_substr.rs): a method on a bare string LITERAL doesn't parse
//! (P001) — the receiver must be a binding, so each test binds the literal first.
//! Convention: a tool returns `0 - <value>`, recovered from the trap by run_neg.

mod common;

use common::run_returning_negative as run_neg;

/// `module tool` body — the `.concat(` token auto-injects `string.sigil`.
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    run_neg(&tool(body))
}

#[test]
fn concat_basic_len_and_mid_byte() {
    // "ab".concat("cd") == "abcd": len 4, byte_at(2) == 'c'(99).
    let body = "    let a: str = \"ab\";\n\
        \x20   let r: str = a.concat(\"cd\");\n\
        \x20   return 0 - (r.len() * 1000 + r.byte_at(2));";
    assert_eq!(neg(body), 4099);
}

#[test]
fn concat_first_and_last_byte() {
    // The seam: byte_at(0) is a's first, byte_at(3) is b's last — proves the two
    // copy loops write the right halves at the right offsets.
    let body = "    let a: str = \"ab\";\n\
        \x20   let r: str = a.concat(\"cd\");\n\
        \x20   return 0 - (r.byte_at(0) * 1000 + r.byte_at(3));";
    // 'a'=97, 'd'=100 → 97100.
    assert_eq!(neg(body), 97100);
}

#[test]
fn concat_empty_right_is_copy_of_left() {
    // a.concat("") — b's copy loop runs zero times; the result is a fresh "ab".
    let body = "    let a: str = \"ab\";\n\
        \x20   let r: str = a.concat(\"\");\n\
        \x20   return 0 - (r.len() * 1000 + r.byte_at(1));";
    // len 2, 'b'=98 → 2098.
    assert_eq!(neg(body), 2098);
}

#[test]
fn concat_empty_left_is_copy_of_right() {
    // "".concat(a) — a's copy loop runs zero times; the result is a fresh "ab".
    let body = "    let e: str = \"\";\n\
        \x20   let a: str = \"ab\";\n\
        \x20   let r: str = e.concat(a);\n\
        \x20   return 0 - (r.len() * 1000 + r.byte_at(0));";
    // len 2, 'a'=97 → 2097.
    assert_eq!(neg(body), 2097);
}

#[test]
fn concat_result_flows_through_substr() {
    // The provenance payoff: an OWNED concat result flows through the BORROWING
    // substr surface for free. "abcd".substr(1, 3) == "bc".
    let body = "    let a: str = \"ab\";\n\
        \x20   let r: str = a.concat(\"cd\");\n\
        \x20   let v: str = r.substr(1, 3);\n\
        \x20   return 0 - (v.byte_at(0) * 1000 + v.len());";
    // 'b'=98, len 2 → 98002.
    assert_eq!(neg(body), 98002);
}

#[test]
fn concat_chains_owned_into_owned() {
    // An owned str is a valid concat INPUT: a.concat("cd").concat("ef") == "abcdef".
    // (Bound stepwise — a method on a call result parses, but stepwise mirrors
    // the literal-receiver idiom and reads clearly.)
    let body = "    let a: str = \"ab\";\n\
        \x20   let r: str = a.concat(\"cd\");\n\
        \x20   let r2: str = r.concat(\"ef\");\n\
        \x20   return 0 - (r2.len() * 1000 + r2.byte_at(5));";
    // len 6, 'f'=102 → 6102.
    assert_eq!(neg(body), 6102);
}
