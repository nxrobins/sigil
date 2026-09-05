//! Owned-strings PR-4: the adversarial-ritual capstone — RUNTIME composition.
//!
//! Owned construction composes with the BORROWING surface (find/split/substr)
//! and with itself (concat/join/itoa chained), and preserves bytes exactly —
//! including multi-byte UTF-8 sequences (AC-2: concat/join neither create nor
//! repair validity; they pass bytes through untouched). Each test EXECUTES the
//! WASM and reads the result back.

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

// ── owned × borrowing: build, then search / split / slice ────────────────────

#[test]
fn concat_then_find() {
    // Build "abcd" by concat, then `find("cd")` on the OWNED result → Some(2).
    let body = "    let a: str = \"ab\";\n\
        \x20   let r: str = a.concat(\"cd\");\n\
        \x20   let p: Option<i64> = r.find(\"cd\");\n\
        \x20   return 0 - p.unwrap_or(99);";
    assert_eq!(neg(body), 2);
}

#[test]
fn concat_then_split_on() {
    // Build "a,b" by concat, then `split_on(",")` → ["a","b"]: 2 segments, seg0=="a".
    let body = "    let pre: str = \"a,\";\n\
        \x20   let r: str = pre.concat(\"b\");\n\
        \x20   let parts: Vec<str> = r.split_on(\",\");\n\
        \x20   let n: i64 = parts.len();\n\
        \x20   let seg0: str = parts.get(0);\n\
        \x20   return 0 - (n * 1000 + seg0.byte_at(0));";
    // n=2, 'a'=97 → 2097.
    assert_eq!(neg(body), 2097);
}

#[test]
fn join_then_substr() {
    // join ["hello","world"] by " " == "hello world", then substr(6,11)=="world".
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let _p0: i64 = v.push(\"hello\");\n\
        \x20   let _p1: i64 = v.push(\"world\");\n\
        \x20   let sep: str = \" \";\n\
        \x20   let r: str = sep.join(v);\n\
        \x20   let w: str = r.substr(6, 11);\n\
        \x20   return 0 - (w.byte_at(0) * 1000 + w.len());";
    // 'w'=119, len 5 → 119005.
    assert_eq!(neg(body), 119005);
}

// ── owned × owned: itoa results joined ───────────────────────────────────────

#[test]
fn itoa_results_joined() {
    // Compose three builders: itoa(1), itoa(2) → join by "-" == "1-2".
    let body = "    let a: i64 = 1;\n\
        \x20   let b: i64 = 2;\n\
        \x20   let v: Vec<str> = Vec::new();\n\
        \x20   let _p0: i64 = v.push(a.itoa());\n\
        \x20   let _p1: i64 = v.push(b.itoa());\n\
        \x20   let sep: str = \"-\";\n\
        \x20   let r: str = sep.join(v);\n\
        \x20   return 0 - (r.len() * 10000 + r.byte_at(0) * 100 + r.byte_at(2));";
    // "1-2": len 3, '1'=49, '2'=50 → 3*10000 + 49*100 + 50 = 34950.
    assert_eq!(neg(body), 34950);
}

// ── AC-2: multi-byte UTF-8 passes through concat/join byte-for-byte ───────────

#[test]
fn utf8_multibyte_survives_concat() {
    // "é" is 2 bytes (0xC3 0xA9); concat with "z" must preserve them exactly —
    // concat copies bytes, never re-encodes (AC-2: preserve, don't create/repair).
    let body = "    let a: str = \"\u{00e9}\";\n\
        \x20   let b: str = \"z\";\n\
        \x20   let r: str = a.concat(b);\n\
        \x20   return 0 - (r.len() * 1000000 + r.byte_at(0) * 1000 + r.byte_at(2));";
    // "éz": len 3, byte0=0xC3=195, byte2='z'=122 → 3*1e6 + 195*1000 + 122 = 3195122.
    assert_eq!(neg(body), 3195122);
}

#[test]
fn utf8_multibyte_survives_join() {
    // join ["é","x"] by "-" == "é-x" == [0xC3,0xA9,0x2D,0x78]: the 2-byte head and
    // the separator land at the right offsets.
    let body = "    let v: Vec<str> = Vec::new();\n\
        \x20   let _p0: i64 = v.push(\"\u{00e9}\");\n\
        \x20   let _p1: i64 = v.push(\"x\");\n\
        \x20   let sep: str = \"-\";\n\
        \x20   let r: str = sep.join(v);\n\
        \x20   return 0 - (r.len() * 1000000 + r.byte_at(0) * 1000 + r.byte_at(3));";
    // "é-x": len 4, byte0=0xC3=195, byte3='x'=120 → 4*1e6 + 195*1000 + 120 = 4195120.
    assert_eq!(neg(body), 4195120);
}
