//! `str` `==` / `!=` and string-literal `match` arms compare BYTES.
//!
//! They used to compare `data_ptr` and never load `len` at all
//! (`emit_str_data_ptr_eq`), which was wrong in two directions at once:
//!
//!   * **False negatives** — two byte-equal strings built at runtime compared
//!     unequal, and a `match` on a constructed scrutinee missed its literal
//!     arm. This is the one the deferral note described.
//!   * **False positives** — `substr` sets `view.data_ptr = parent.data_ptr +
//!     start`, so `s.substr(0, k) == s` was TRUE for every k. That one was not
//!     in the note; comparing pointers without lengths is not "identity", it is
//!     "shares a starting address".
//!
//! Both were silent: no diagnostic, no trap, just a wrong answer.
//!
//! The cases below are chosen as detectors, not for coverage. The empty and
//! one-byte pairs catch a wrong memory offset (a `+4` copied from the array
//! scan would read past short strings); the both-orders unequal pairs catch a
//! comparison driven by only one side's length; the `substr` pairs are the
//! false-positive and false-negative fixes respectively.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

fn tool(effects: &str, body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {effects} {{\n{body}\n}}\n"
    )
}

fn neg(effects: &str, body: &str) -> i64 {
    let result = compile_tool(&tool(effects, body)).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a clean negative-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected negative sentinel"),
    }
}

/// 1 = equal, 2 = unequal.
const EQ: &str = "    if e { return 0 - 1; } else { return 0 - 2; }";

/// Two `str` locals compared with `op`, no allocation.
fn cmp_lit(a: &str, b: &str, op: &str) -> i64 {
    let body = format!(
        "    let x: str = \"{a}\";\n\
         \x20   let y: str = \"{b}\";\n\
         \x20   let e: bool = x {op} y;\n{EQ}"
    );
    neg("", &body)
}

#[test]
fn equal_literals_compare_equal() {
    assert_eq!(cmp_lit("hello", "hello", "=="), 1);
}

#[test]
fn unequal_same_length_compare_unequal() {
    assert_eq!(cmp_lit("abc", "abd", "=="), 2);
}

/// Both orders: a comparison that scanned only the left length would call
/// `"abc" == "abcd"` equal in one direction and not the other.
#[test]
fn unequal_different_length_compares_unequal_both_ways() {
    assert_eq!(cmp_lit("abc", "abcd", "=="), 2, "shorter on the left");
    assert_eq!(cmp_lit("abcd", "abc", "=="), 2, "longer on the left");
}

#[test]
fn two_empty_strings_compare_equal() {
    assert_eq!(cmp_lit("", "", "=="), 1);
}

/// Empty vs one byte, both orders — the offset detector. With a stray `+4` on
/// the loads these read past the content entirely.
#[test]
fn empty_and_nonempty_compare_unequal_both_ways() {
    assert_eq!(cmp_lit("", "a", "=="), 2);
    assert_eq!(cmp_lit("a", "", "=="), 2);
}

#[test]
fn single_byte_strings_compare_by_content() {
    assert_eq!(cmp_lit("a", "a", "=="), 1);
    assert_eq!(cmp_lit("a", "b", "=="), 2);
}

#[test]
fn not_equal_is_the_negation() {
    assert_eq!(cmp_lit("abc", "abd", "!="), 1, "differing → != is true");
    assert_eq!(cmp_lit("abc", "abc", "!="), 2, "identical → != is false");
}

/// The FALSE POSITIVE fix. `substr` shares the parent's starting address, so
/// pointer comparison called a prefix equal to its parent.
#[test]
fn a_substr_view_is_not_equal_to_its_parent() {
    let body = format!(
        "    let s: str = \"fnx\";\n\
         \x20   let v: str = s.substr(0, 2);\n\
         \x20   let e: bool = v == s;\n{EQ}"
    );
    assert_eq!(neg("", &body), 2);
}

/// The FALSE NEGATIVE fix. A view over the first two bytes of `"fnx"` is
/// byte-equal to the literal `"fn"` but has a different address.
#[test]
fn a_substr_view_equals_a_literal_with_the_same_bytes() {
    let body = format!(
        "    let s: str = \"fnx\";\n\
         \x20   let v: str = s.substr(0, 2);\n\
         \x20   let lit: str = \"fn\";\n\
         \x20   let e: bool = v == lit;\n{EQ}"
    );
    assert_eq!(neg("", &body), 1);
}

/// `match` on a string literal shares the one comparison primitive, so it gets
/// the fix too. A view scrutinee previously missed its arm and fell to `_`.
#[test]
fn match_on_a_string_literal_matches_a_view_scrutinee() {
    let body = "    let s: str = \"fnx\";\n\
                \x20   let v: str = s.substr(0, 2);\n\
                \x20   match v {\n\
                \x20       \"fn\" => { return 0 - 1; },\n\
                \x20       _ => { return 0 - 2; },\n\
                \x20   }";
    assert_eq!(neg("", body), 1);
}

/// The same match must still REJECT a scrutinee that merely starts with the
/// arm's text — length is part of the comparison.
#[test]
fn match_on_a_string_literal_rejects_a_longer_scrutinee() {
    let body = "    let s: str = \"fnx\";\n\
                \x20   match s {\n\
                \x20       \"fn\" => { return 0 - 1; },\n\
                \x20       _ => { return 0 - 2; },\n\
                \x20   }";
    assert_eq!(neg("", body), 2);
}

// ── Property-based: `==` agrees with `bytes_eq` on every input ────────────────
//
// `str.bytes_eq` (= `len() ==` + `starts_with`) predates this fix and byte-compares by
// construction; `==` now lowers to the same predicate as one AIR statement. The property
// pins that agreement over random inputs rather than the hand-picked detectors above.
// Both verdicts are read out of ONE run — r = (a==b ? 1 : 2) + (a.bytes_eq(b) ? 10 : 20) —
// so agreement is exactly r ∈ {11, 22}, and a 12 or 21 names which side flipped.
mod props {
    use super::*;
    use proptest::prelude::*;

    fn both_verdicts(a: &str, b: &str) -> i64 {
        let body = format!(
            "    let x: str = \"{a}\";\n\
             \x20   let y: str = \"{b}\";\n\
             \x20   let e: bool = x == y;\n\
             \x20   let f: bool = x.bytes_eq(y);\n\
             \x20   let mut r: i64 = 0;\n\
             \x20   if e {{ r = 1; }} else {{ r = 2; }}\n\
             \x20   if f {{ r = r + 10; }} else {{ r = r + 20; }}\n\
             \x20   return 0 - r;"
        );
        neg("", &body)
    }

    proptest! {
        // Each case is a full compile + execute, so the case count is small on purpose.
        #![proptest_config(ProptestConfig { cases: 24, ..ProptestConfig::default() })]

        /// Random pairs are almost always unequal — this leg pins the unequal half.
        #[test]
        fn eq_and_bytes_eq_agree_on_random_pairs(a in "[a-c]{0,8}", b in "[a-c]{0,8}") {
            let r = both_verdicts(&a, &b);
            prop_assert!(r == 11 || r == 22, "`==` and `bytes_eq` disagree (r={}) on {:?} vs {:?}", r, a, b);
        }

        /// The equal half, guaranteed: the same text at two distinct literal sites.
        #[test]
        fn eq_and_bytes_eq_agree_on_identical_texts(a in "[a-c]{0,8}") {
            let r = both_verdicts(&a, &a);
            prop_assert_eq!(r, 11, "byte-identical strings must be `==` AND `bytes_eq`");
        }
    }
}
