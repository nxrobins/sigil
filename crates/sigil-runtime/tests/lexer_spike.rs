//! L0 spike — the verify-first gate for a SIGIL-written lexer.
//!
//! Before writing any lexer code, prove the two foundation questions a lexer
//! rests on, so L1 is decided against facts rather than predictions:
//!
//!   GATE A — `Vec<Record>` monomorphizes. We've shipped `Vec<i64>` and
//!   `Vec<str>` (pointer-width elements). A `record` is also a heap pointer, so
//!   `Vec<Token>` *should* monomorphize identically — but it has never been
//!   done. These tests push/get a multi-field `Token`, read every field back,
//!   and (the real lexer data path) `substr` the source by a stored token span.
//!
//!   GATE B — keyword recognition on a `substr` VIEW. The lexer recognises
//!   keywords by comparing an identifier span against literals. When this spike
//!   ran, `str ==` (`air.rs` `emit_str_data_ptr_eq`) compared ONLY the header
//!   `data_ptr` fields — the byte-by-byte form was deferred (AG-S1-M) — so
//!   `view == "fn"` was FALSE even when the bytes matched, and the lexer needed
//!   the `str.bytes_eq` helper (= `len() == k && starts_with(kw)`, shipped this
//!   PR). PR #699 has since made `==` byte-compare; the tests below now pin the
//!   NEW semantics, and `bytes_eq` stays as the house idiom the lexer uses.
//!
//! Harness mirrors `str_stress.rs` / `map_stress.rs`: a `tool` returns
//! `0 - value`, recovered via the negative-sentinel convention.

mod common;

use common::run_returning_negative as run_neg;

/// Wrap a body with optional top-level definitions (a `record`, helpers).
fn tool_with_defs(defs: &str, body: &str) -> String {
    format!(
        "module tool;\n{defs}\n\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg_defs(defs: &str, body: &str) -> i64 {
    run_neg(&tool_with_defs(defs, body))
}

/// No extra defs — a bare body.
fn neg(body: &str) -> i64 {
    run_neg(&tool_with_defs("", body))
}

const TOKEN: &str = "record Token { kind: i64, start: i64, end: i64 }";

// ── GATE A: Vec<Record> monomorphizes ────────────────────────────────────────

#[test]
fn vec_of_records_roundtrips_every_field() {
    // Push two DISTINCT tokens, get them back, and read all six fields through a
    // positional checksum (each single-digit field occupies its own decimal
    // place, so any corrupted field perturbs a specific digit).
    //   t0 = {kind:1, start:0, end:2}   t1 = {kind:7, start:3, end:9}
    //   cks = k0 + s0*10 + e0*100 + k1*1000 + s1*10000 + e1*100000
    //       = 1 + 0 + 200 + 7000 + 30000 + 900000 = 937201
    //   return len*1_000_000 + cks = 2_937_201
    let body = "    let mut toks: Vec<Token> = Vec::new();\n\
        \x20   let t0: Token = Token { kind: 1, start: 0, end: 2 };\n\
        \x20   let n0: i64 = toks.push(t0);\n\
        \x20   let t1: Token = Token { kind: 7, start: 3, end: 9 };\n\
        \x20   let n1: i64 = toks.push(t1);\n\
        \x20   let g0: Token = toks.get(0);\n\
        \x20   let g1: Token = toks.get(1);\n\
        \x20   let cks: i64 = g0.kind + g0.start * 10 + g0.end * 100 + g1.kind * 1000 + g1.start * 10000 + g1.end * 100000;\n\
        \x20   return 0 - (toks.len() * 1000000 + cks);";
    assert_eq!(neg_defs(TOKEN, body), 2_937_201);
}

#[test]
fn token_span_substr_recovers_source_text() {
    // The actual lexer data path: a token stores a [start,end) span into the
    // source; recovering the token text is `src.substr(t.start, t.end)`. Push
    // two spans over "fnxy", get the second, substr the source by its span, and
    // read the recovered view. t1 spans [2,4) → "xy": len 2, byte_at(0) = 'x'(120).
    let body = "    let src: str = \"fnxy\";\n\
        \x20   let mut toks: Vec<Token> = Vec::new();\n\
        \x20   let t0: Token = Token { kind: 1, start: 0, end: 2 };\n\
        \x20   let a: i64 = toks.push(t0);\n\
        \x20   let t1: Token = Token { kind: 2, start: 2, end: 4 };\n\
        \x20   let b: i64 = toks.push(t1);\n\
        \x20   let got: Token = toks.get(1);\n\
        \x20   let view: str = src.substr(got.start, got.end);\n\
        \x20   return 0 - (view.len() * 1000 + view.byte_at(0));";
    assert_eq!(neg_defs(TOKEN, body), 2120);
}

#[test]
fn vec_of_records_scales_and_reads_back() {
    // A small loop builds N tokens whose `kind` encodes the index, then reads
    // every one back and sums the kinds — proves push-in-a-loop + get across a
    // grow (Vec reallocs as it passes its initial capacity), not just two slots.
    // kind(i) = i, Σ_{0..N} i = N*(N-1)/2. N=20 → 190.
    let body = "    let mut toks: Vec<Token> = Vec::new();\n\
        \x20   let mut i: i64 = 0;\n\
        \x20   while i < 20 {\n\
        \x20       let t: Token = Token { kind: i, start: i, end: i };\n\
        \x20       let n: i64 = toks.push(t);\n\
        \x20       i = i + 1;\n\
        \x20   }\n\
        \x20   let mut sum: i64 = 0;\n\
        \x20   let mut k: i64 = 0;\n\
        \x20   let np: i64 = toks.len();\n\
        \x20   while k < np {\n\
        \x20       let g: Token = toks.get(k);\n\
        \x20       sum = sum + g.kind;\n\
        \x20       k = k + 1;\n\
        \x20   }\n\
        \x20   return 0 - (np * 1000 + sum);";
    // 20 tokens, Σkind = 190 → 20*1000 + 190 = 20190.
    assert_eq!(neg_defs(TOKEN, body), 20190);
}

// ── GATE B: keyword recognition on a substr view ─────────────────────────────

#[test]
fn operator_eq_on_interned_literals_works() {
    // Sanity: two interned literals are `==`. Under the retired data-ptr fast
    // path this held because they SHARED a data_ptr; since PR #699 it holds
    // because the bytes match. Same verdict, different reason — kept as the
    // baseline the view case below contrasts against.
    let body = "    let a: str = \"fn\";\n\
        \x20   let b: str = \"fn\";\n\
        \x20   if a == b {\n\
        \x20       return 0 - 1;\n\
        \x20   } else {\n\
        \x20       return 0 - 2;\n\
        \x20   }";
    assert_eq!(neg(body), 1);
}

#[test]
fn operator_eq_on_a_view_byte_compares() {
    // THE GAP, now closed. A substr view of "fn" compared to the literal "fn"
    // via `==` returns TRUE: the comparison is byte-wise, so the view's
    // data_ptr pointing into "fnx" rather than at the interned "fn" no longer
    // matters. This assertion read 2 while the N12-S1 / AG-S1-M deferral stood,
    // and its comment pre-authorized exactly this flip.
    //
    // The lexer may now use `==` for keyword recognition. It still uses
    // `bytes_eq`, which computes the same predicate — that is a house-dialect
    // choice, no longer a correctness requirement.
    let body = "    let s: str = \"fnx\";\n\
        \x20   let v: str = s.substr(0, 2);\n\
        \x20   if v == \"fn\" {\n\
        \x20       return 0 - 1;\n\
        \x20   } else {\n\
        \x20       return 0 - 2;\n\
        \x20   }";
    assert_eq!(neg(body), 1);
}

/// `is_keyword(v, kw)` modelled as `len()==klen && starts_with(kw)`, encoded:
///   r = (starts_with(kw) ? 1 : 0) + (len()==klen ? 10 : 20)
///   11 = MATCH · 21 = starts-with but wrong length · 10 = right length, no prefix
fn kw_probe(view_src: &str, sub_end: i64, kw: &str, klen: i64) -> i64 {
    let body = format!(
        "    let s: str = \"{view_src}\";\n\
         \x20   let v: str = s.substr(0, {sub_end});\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   if v.starts_with(\"{kw}\") {{\n\
         \x20       r = 1;\n\
         \x20   }} else {{\n\
         \x20       r = 0;\n\
         \x20   }}\n\
         \x20   if v.len() == {klen} {{\n\
         \x20       r = r + 10;\n\
         \x20   }} else {{\n\
         \x20       r = r + 20;\n\
         \x20   }}\n\
         \x20   return 0 - r;"
    );
    neg(&body)
}

#[test]
fn keyword_match_via_len_and_starts_with_on_a_view() {
    // v = "fnx".substr(0,2) = "fn" (a VIEW). Against keyword "fn" (len 2):
    // starts_with → true, len==2 → true ⇒ 11 = MATCH. This is the lexer's path.
    assert_eq!(kw_probe("fnx", 2, "fn", 2), 11);
}

#[test]
fn keyword_len_guard_rejects_a_proper_prefix() {
    // v = "fnx".substr(0,3) = "fnx" (len 3). Against keyword "fn": starts_with →
    // true, but len==2 → false ⇒ 21. The length guard is load-bearing: without
    // it, "fnx" would be mis-recognised as the keyword "fn".
    assert_eq!(kw_probe("fnx", 3, "fn", 2), 21);
}

#[test]
fn keyword_prefix_guard_rejects_right_length_wrong_bytes() {
    // v = "xy".substr(0,2) = "xy" (len 2). Against keyword "fn": len==2 → true,
    // but starts_with("fn") → false ⇒ 10. Right length alone is not enough.
    assert_eq!(kw_probe("xy", 2, "fn", 2), 10);
}

// ── GATE B′: `str.bytes_eq` — the keyword byte-compare, as ONE method ─────────
// `bytes_eq` (= `len == && starts_with`) wraps the GATE-B workaround into the
// single call the lexer's keyword path uses. 1 = equal, 2 = not-equal.

#[test]
fn bytes_eq_matches_a_view_against_a_literal() {
    // v = "fnx".substr(0,2) = "fn" (a VIEW). `v.bytes_eq("fn")` → TRUE — exactly
    // where `==` returned false above. This is the lexer's keyword path.
    let body = "    let s: str = \"fnx\";\n\
        \x20   let v: str = s.substr(0, 2);\n\
        \x20   if v.bytes_eq(\"fn\") { return 0 - 1; } else { return 0 - 2; }";
    assert_eq!(neg(body), 1);
}

#[test]
fn bytes_eq_len_guard_rejects_a_proper_prefix() {
    // v = "fnx".substr(0,3) = "fnx" (len 3). `v.bytes_eq("fn")` → FALSE: the
    // length guard rejects it (a bare `starts_with` would mis-accept "fnx").
    let body = "    let s: str = \"fnx\";\n\
        \x20   let v: str = s.substr(0, 3);\n\
        \x20   if v.bytes_eq(\"fn\") { return 0 - 1; } else { return 0 - 2; }";
    assert_eq!(neg(body), 2);
}

#[test]
fn bytes_eq_rejects_right_length_wrong_bytes() {
    // v = "xy".substr(0,2) = "xy" (len 2). `v.bytes_eq("fn")` → FALSE: right
    // length, wrong bytes.
    let body = "    let s: str = \"xy\";\n\
        \x20   let v: str = s.substr(0, 2);\n\
        \x20   if v.bytes_eq(\"fn\") { return 0 - 1; } else { return 0 - 2; }";
    assert_eq!(neg(body), 2);
}

#[test]
fn bytes_eq_on_interned_literals_also_byte_compares() {
    // `bytes_eq` is byte-based, so it agrees with `==` on the easy interned case
    // too: "fn".bytes_eq("fn") → TRUE.
    let body = "    let a: str = \"fn\";\n\
        \x20   if a.bytes_eq(\"fn\") { return 0 - 1; } else { return 0 - 2; }";
    assert_eq!(neg(body), 1);
}
