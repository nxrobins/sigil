//! `from_bytes` (PR S3): validate untrusted bytes into a `str`.
//!
//! `ptr.from_bytes(len) -> Option<str>` validates `[ptr, ptr+len)` as UTF-8 and,
//! on success, returns an OWNED `str` (a fresh-alloc'd COPY of the bytes — never a
//! view aliasing the input, ET-1). `ptr.valid_up_to(len) -> i64` is the rail: the
//! count of leading valid bytes (`== len` iff fully valid, else the offset of the
//! first invalid sequence — Rust's `Utf8Error::valid_up_to`).
//!
//! Both are i64-receiver methods (mirroring `.itoa()`) → `string::str_from_bytes`
//! / `string::str_valid_up_to`. The `.from_bytes(` token ambiently injects
//! `string.sigil` (+ transitive `option.sigil`).
//!
//! Test convention: tools return a NEGATIVE sentinel (`0 - value`) that the
//! runtime reports as `Err(Trapped { "tool returned error (value)" })`; `neg`
//! recovers `value` and PANICS on a genuine wasm trap (so a clean test is also a
//! "did NOT trap" assertion — ET-5's free trap detector). Bytes are built in-tool
//! via `alloc` + `store8`, then passed to `from_bytes` as `(buf, n)`.

mod common;

use common::run_returning_negative_with_fuel;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// This suite pins UTF-8 validation SEMANTICS. The validator's scan loop is
/// data-dependent (input length), so its `recommended_budget` is honestly a
/// straight-line FLOOR — under fuel ENFORCEMENT a large input legitimately
/// fuel-traps at the bare recommendation (`large_input_terminates` did, at
/// 500 iterations). Run at an explicit POLICY budget instead (the bounded_map
/// `neg` precedent): termination is still enforced — a non-advancing scan
/// branch burns this finite budget and traps, which is exactly the hang
/// detector `large_input_terminates` wants.
const SEMANTICS_FUEL: u64 = 1_000_000;

fn neg(body: &str) -> i64 {
    run_returning_negative_with_fuel(&tool(body), SEMANTICS_FUEL)
}

/// Emit a tool prelude that builds `bytes` into a fresh `buf` via `alloc` + `store8`
/// and binds `n = bytes.len()`. The tool then calls `buf.from_bytes(n)` /
/// `buf.valid_up_to(n)` (the PUBLIC methods) on the untrusted buffer.
fn build(bytes: &[u8]) -> String {
    let mut s = format!("    let buf: i64 = alloc({});\n", bytes.len());
    for (i, b) in bytes.iter().enumerate() {
        s.push_str(&format!("    store8(buf + {i}, {b});\n"));
    }
    s.push_str(&format!("    let n: i64 = {};\n", bytes.len()));
    s
}

/// `from_bytes(bytes)` must be `Some`; returns `len*1000 + byte_at(0)` (so a wrong
/// result is obvious). Bytes must be non-empty (reads byte 0).
fn some_lenbyte(bytes: &[u8]) -> i64 {
    let body = format!(
        "{}    let o: Option<str> = buf.from_bytes(n);\n\
         \x20   match o {{\n\
         \x20       Some(s) => {{ return 0 - (s.len() * 1000 + s.byte_at(0)); }},\n\
         \x20       None => {{ return 0 - 9999; }}\n\
         \x20   }}",
        build(bytes)
    );
    neg(&body)
}

/// `from_bytes(bytes)` must be `None`; returns 1 on None, else `8000 + len` (so a
/// wrongly-accepted invalid is obvious).
fn is_none(bytes: &[u8]) -> i64 {
    let body = format!(
        "{}    let o: Option<str> = buf.from_bytes(n);\n\
         \x20   match o {{\n\
         \x20       Some(s) => {{ return 0 - (8000 + s.len()); }},\n\
         \x20       None => {{ return 0 - 1; }}\n\
         \x20   }}",
        build(bytes)
    );
    neg(&body)
}

/// `buf.valid_up_to(n)` — the leading-valid-byte count (== len iff fully valid).
fn valid_up_to(bytes: &[u8]) -> i64 {
    let body = format!(
        "{}    let k: i64 = buf.valid_up_to(n);\n    return 0 - (k + 1000);",
        build(bytes)
    );
    neg(&body) - 1000
}

/// `from_bytes(bytes)` must be `Some`; returns just `len` (safe for the empty str,
/// which `some_lenbyte` can't read).
fn some_len(bytes: &[u8]) -> i64 {
    let body = format!(
        "{}    let o: Option<str> = buf.from_bytes(n);\n\
         \x20   match o {{\n\
         \x20       Some(s) => {{ return 0 - (s.len() + 7); }},\n\
         \x20       None => {{ return 0 - 9999; }}\n\
         \x20   }}",
        build(bytes)
    );
    neg(&body) - 7
}

// ── ET-7: the Option<str> monomorphization spike (the gate) ──────────────────

#[test]
fn option_str_monomorph_spike() {
    // Construct Some(s) at the `str` type, match it, read the inner bytes back.
    // This is the FIRST proof that Option<str> monomorphizes end-to-end — before
    // any validator logic relies on it.
    let body = "    let a: str = \"hi\";\n\
        \x20   let o: Option<str> = Some(a);\n\
        \x20   match o {\n\
        \x20       Some(s) => { return 0 - (s.len() * 1000 + s.byte_at(0)); },\n\
        \x20       None => { return 0 - 9999; }\n\
        \x20   }";
    // "hi": len 2, 'h'=104 → 2*1000 + 104 = 2104.
    assert_eq!(neg(body), 2104);
}

// ── VALID: 1/2/3/4-byte, mixed, empty, class boundaries → Some ───────────────

#[test]
fn valid_ascii_and_multibyte() {
    assert_eq!(some_lenbyte(&[0x41]), 1065); // "A": len 1, byte0 65
    assert_eq!(some_lenbyte(&[0xC3, 0xA9]), 2195); // "é": len 2, byte0 195
    assert_eq!(some_lenbyte(&[0xE2, 0x82, 0xAC]), 3226); // "€": len 3, byte0 226
    assert_eq!(some_lenbyte(&[0xF0, 0x9F, 0x98, 0x80]), 4240); // "😀": len 4, byte0 240
    // "a€b" = 0x61 0xE2 0x82 0xAC 0x62 → len 5, byte0 97.
    assert_eq!(some_lenbyte(&[0x61, 0xE2, 0x82, 0xAC, 0x62]), 5097);
}

#[test]
fn valid_empty_is_some() {
    // Empty input is valid UTF-8 (the empty string), RFC/Rust-correct → Some("").
    assert_eq!(some_len(&[]), 0);
    assert_eq!(valid_up_to(&[]), 0); // == len(0): fully valid.
}

#[test]
fn valid_class_boundaries() {
    // Smallest/largest VALID per multi-byte class (ET-6 edges that must be Some).
    assert_eq!(some_lenbyte(&[0xC2, 0x80]), 2194); // U+0080, smallest 2-byte
    assert_eq!(some_lenbyte(&[0xED, 0x9F, 0xBF]), 3237); // U+D7FF, last pre-surrogate
    assert_eq!(some_lenbyte(&[0xF4, 0x8F, 0xBF, 0xBF]), 4244); // U+10FFFF, last valid
    assert_eq!(some_lenbyte(&[0xEE, 0x80, 0x80]), 3238); // U+E000, first post-surrogate
}

// ── ET-6: INVALID classes → None ─────────────────────────────────────────────

#[test]
fn invalid_overlong() {
    assert_eq!(is_none(&[0xC0, 0x80]), 1); // 2-byte overlong (lead < 0xC2)
    assert_eq!(is_none(&[0xC1, 0xBF]), 1); // 2-byte overlong
    assert_eq!(is_none(&[0xE0, 0x80, 0x80]), 1); // 3-byte overlong (c1 < 0xA0)
    assert_eq!(is_none(&[0xF0, 0x80, 0x80, 0x80]), 1); // 4-byte overlong (c1 < 0x90)
}

#[test]
fn invalid_surrogate_and_range() {
    assert_eq!(is_none(&[0xED, 0xA0, 0x80]), 1); // U+D800 surrogate (c1 > 0x9F)
    assert_eq!(is_none(&[0xED, 0xBF, 0xBF]), 1); // U+DFFF surrogate
    assert_eq!(is_none(&[0xF4, 0x90, 0x80, 0x80]), 1); // > U+10FFFF (c1 > 0x8F)
    assert_eq!(is_none(&[0xF5, 0x80, 0x80, 0x80]), 1); // lead > 0xF4
}

#[test]
fn invalid_orphan_and_stray() {
    assert_eq!(is_none(&[0x80]), 1); // lone continuation
    assert_eq!(is_none(&[0xBF]), 1); // lone continuation (top)
    assert_eq!(is_none(&[0xFF]), 1); // never a valid byte
    assert_eq!(is_none(&[0xE2, 0x82, 0x41]), 1); // 3-byte with bad final continuation
    assert_eq!(is_none(&[0x41, 0x80]), 1); // ASCII then orphan
}

// ── ET-5: truncated trailing sequences → None, NOT a trap ────────────────────
// `neg` PANICS on a genuine wasm trap, so these passing IS the no-trap proof.

#[test]
fn truncated_sequences_are_none_not_trap() {
    assert_eq!(is_none(&[0xC3]), 1); // 2-byte head, no continuation
    assert_eq!(is_none(&[0xE2, 0x82]), 1); // 3-byte head, one short
    assert_eq!(is_none(&[0xF0, 0x9F, 0x98]), 1); // 4-byte head, one short
    assert_eq!(is_none(&[0x41, 0xE2]), 1); // valid prefix then truncated head
}

// ── ET-1: the result is an OWNED copy, not a view aliasing the input ──────────

#[test]
fn result_is_owned_copy_survives_input_overwrite() {
    // Build "€" in buf, from_bytes → Some(s), then OVERWRITE buf. If `s` aliased
    // the input, its bytes would change; an owned copy is unaffected.
    let body = "    let buf: i64 = alloc(3);\n\
        \x20   store8(buf + 0, 226);\n\
        \x20   store8(buf + 1, 130);\n\
        \x20   store8(buf + 2, 172);\n\
        \x20   let o: Option<str> = buf.from_bytes(3);\n\
        \x20   match o {\n\
        \x20       Some(s) => {\n\
        \x20           store8(buf + 0, 88);\n\
        \x20           store8(buf + 1, 88);\n\
        \x20           store8(buf + 2, 88);\n\
        \x20           return 0 - (s.byte_at(0) * 1000 + s.len());\n\
        \x20       },\n\
        \x20       None => { return 0 - 9999; }\n\
        \x20   }";
    // s must STILL read 0xE2(226), len 3 → 226003 (88003 would mean it aliased).
    assert_eq!(neg(body), 226003);
}

#[test]
fn result_composes_with_substr() {
    // A from_bytes result flows through the borrowing surface for free: "a€b" →
    // Some(s) → s.substr(1,4) == "€" (a valid codepoint boundary).
    let body = "    let buf: i64 = alloc(5);\n\
        \x20   store8(buf + 0, 97);\n\
        \x20   store8(buf + 1, 226);\n\
        \x20   store8(buf + 2, 130);\n\
        \x20   store8(buf + 3, 172);\n\
        \x20   store8(buf + 4, 98);\n\
        \x20   let o: Option<str> = buf.from_bytes(5);\n\
        \x20   match o {\n\
        \x20       Some(s) => {\n\
        \x20           let mid: str = s.substr(1, 4);\n\
        \x20           return 0 - (mid.byte_at(0) * 1000 + mid.len());\n\
        \x20       },\n\
        \x20       None => { return 0 - 9999; }\n\
        \x20   }";
    assert_eq!(neg(body), 226003); // "€": byte0 226, len 3
}

// ── ET-2: valid_up_to returns the EXACT offset (a len-or-0 stub reds here) ────

#[test]
fn valid_up_to_exact_offsets() {
    // A bad byte at index 1, 4, 7 of otherwise-valid ASCII → that exact offset.
    assert_eq!(valid_up_to(&[65, 0x80, 65]), 1);
    assert_eq!(valid_up_to(&[65, 65, 65, 65, 0x80]), 4);
    assert_eq!(valid_up_to(&[65, 65, 65, 65, 65, 65, 65, 0x80]), 7);
    // Offset lands at the START of a bad multibyte, not mid-sequence:
    assert_eq!(valid_up_to(&[0xE2, 0x82, 0xAC, 0xFF]), 3); // valid € then 0xFF at 3
    assert_eq!(valid_up_to(&[65, 0xC3]), 1); // 'A' then truncated head at 1
}

#[test]
fn rail_floor_oracle() {
    // from_bytes(b).is_some() == (valid_up_to(b) == len) over the whole corpus —
    // the rail and the floor never disagree.
    let corpus: &[&[u8]] = &[
        &[],
        &[0x41],
        &[0xC3, 0xA9],
        &[0xE2, 0x82, 0xAC],
        &[0xF0, 0x9F, 0x98, 0x80],
        &[0x61, 0xE2, 0x82, 0xAC, 0x62],
        &[0xC2, 0x80],
        &[0xED, 0x9F, 0xBF],
        &[0xF4, 0x8F, 0xBF, 0xBF],
        &[0xC0, 0x80],
        &[0xE0, 0x80, 0x80],
        &[0xED, 0xA0, 0x80],
        &[0xF4, 0x90, 0x80, 0x80],
        &[0x80],
        &[0xFF],
        &[0xC3],
        &[0xE2, 0x82],
        &[0x41, 0x80],
    ];
    for b in corpus {
        let some = is_none(b) != 1; // from_bytes is Some
        let vut = valid_up_to(b);
        assert_eq!(
            some,
            vut == b.len() as i64,
            "oracle mismatch for {b:02X?}: is_some={some} valid_up_to={vut} len={}",
            b.len()
        );
    }
}

// ── ET-3: pathological / large input terminates within fuel ──────────────────

#[test]
fn large_input_terminates() {
    // 500 valid 2-byte codepoints = 1000 bytes; the scan advances by 2 each of 500
    // iterations and completes within fuel (no hang). A non-advancing branch would
    // exhaust fuel → a trap → `neg`/`valid_up_to` would panic.
    let mut v = Vec::new();
    for _ in 0..500 {
        v.push(0xC3);
        v.push(0xA9);
    }
    assert_eq!(valid_up_to(&v), 1000);
    assert_eq!(some_len(&v), 1000);
    // A long all-continuation run rejects immediately (bad at 0) and also terminates.
    let junk = vec![0x80u8; 1000];
    assert_eq!(valid_up_to(&junk), 0);
    assert_eq!(is_none(&junk), 1);
}

// ── ET-4: negative len is rejected before any forge ──────────────────────────

#[test]
fn negative_len_is_none() {
    // from_bytes(ptr, -1) → None (no forge); valid_up_to(ptr, -1) → 0.
    let from = "    let buf: i64 = alloc(4);\n\
        \x20   store8(buf + 0, 65);\n\
        \x20   let n: i64 = 0 - 1;\n\
        \x20   let o: Option<str> = buf.from_bytes(n);\n\
        \x20   match o {\n\
        \x20       Some(s) => { return 0 - (8000 + s.len()); },\n\
        \x20       None => { return 0 - 1; }\n\
        \x20   }";
    assert_eq!(neg(from), 1);
    let vut = "    let buf: i64 = alloc(4);\n\
        \x20   let n: i64 = 0 - 1;\n\
        \x20   let k: i64 = buf.valid_up_to(n);\n\
        \x20   return 0 - (k + 1000);";
    assert_eq!(neg(vut) - 1000, 0);
}
