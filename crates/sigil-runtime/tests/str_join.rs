//! Owned-strings PR-3: `sep.join(pieces)` — join a `Vec<str>` with a separator.
//!
//! `sep.join(pieces)` desugars to `string::str_join(sep, pieces)`. It sums the
//! piece lengths plus `(n-1)*sep.len()` separators (the `(n-1)` GUARDED by
//! `n > 0` so the empty vector can't underflow — ET-4), allocates ONCE, then
//! copies each piece with `sep` between. These tests build a `Vec<str>` and
//! execute the join, exercising both `string.sigil`'s `str_join` and the
//! transitive `vec.sigil` injection it now requires.

mod common;

use common::run_returning_negative as run_neg;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    run_neg(&tool(body))
}

#[test]
fn join_two_pieces_single_sep() {
    // ["ab","cd"] joined by "-" == "ab-cd": len 5, byte_at(2) == '-'(45).
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let p0: i64 = v.push(\"ab\");\n\
        \x20   let p1: i64 = v.push(\"cd\");\n\
        \x20   let sep: str = \"-\";\n\
        \x20   let r: str = sep.join(v);\n\
        \x20   return 0 - (r.len() * 1000 + r.byte_at(2));";
    assert_eq!(neg(body), 5045);
}

#[test]
fn join_piece_and_sep_bytes() {
    // Cross-check a piece byte AND a separator byte land where expected:
    // "ab-cd" byte_at(0)=='a'(97), byte_at(2)=='-'(45).
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let p0: i64 = v.push(\"ab\");\n\
        \x20   let p1: i64 = v.push(\"cd\");\n\
        \x20   let sep: str = \"-\";\n\
        \x20   let r: str = sep.join(v);\n\
        \x20   return 0 - (r.byte_at(0) * 1000 + r.byte_at(2));";
    // 'a'=97, '-'=45 → 97045.
    assert_eq!(neg(body), 97045);
}

#[test]
fn join_empty_vec_is_empty() {
    // ET-4 boundary n=0: join of zero pieces is "" (the (n-1) term is guarded,
    // so no underflow). len 0.
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let sep: str = \"-\";\n\
        \x20   let r: str = sep.join(v);\n\
        \x20   return 0 - (r.len() + 100);";
    assert_eq!(neg(body), 100);
}

#[test]
fn join_one_piece_no_separator() {
    // ET-4 boundary n=1: a single piece, no separator — a fresh copy of "xy"
    // (NOT the input itself → no T253). len 2, byte_at(1)=='y'(121).
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let p0: i64 = v.push(\"xy\");\n\
        \x20   let sep: str = \"-\";\n\
        \x20   let r: str = sep.join(v);\n\
        \x20   return 0 - (r.len() * 1000 + r.byte_at(1));";
    assert_eq!(neg(body), 2121);
}

#[test]
fn join_multichar_separator() {
    // A 2-byte separator between 3 single-byte pieces: ["a","b","c"] by ", "
    // == "a, b, c" (len 7). Confirms (n-1)*sep.len() = 2*2 = 4 separator bytes.
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let p0: i64 = v.push(\"a\");\n\
        \x20   let p1: i64 = v.push(\"b\");\n\
        \x20   let p2: i64 = v.push(\"c\");\n\
        \x20   let sep: str = \", \";\n\
        \x20   let r: str = sep.join(v);\n\
        \x20   return 0 - (r.len() * 1000 + r.byte_at(3));";
    // "a, b, c": len 7, byte_at(3)=='b'(98) → 7098.
    assert_eq!(neg(body), 7098);
}

#[test]
fn join_empty_separator_is_concat() {
    // An empty separator degenerates to concatenation: ["ab","cd"] by "" =="abcd".
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let p0: i64 = v.push(\"ab\");\n\
        \x20   let p1: i64 = v.push(\"cd\");\n\
        \x20   let sep: str = \"\";\n\
        \x20   let r: str = sep.join(v);\n\
        \x20   return 0 - (r.len() * 1000 + r.byte_at(3));";
    // "abcd": len 4, byte_at(3)=='d'(100) → 4100.
    assert_eq!(neg(body), 4100);
}
