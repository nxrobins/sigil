//! UTF-8 boundary enforcement: `substr` traps on a non-boundary slice.
//!
//! `substr(start, end)` now traps if `start` or `end` lands inside a multi-byte
//! codepoint (a continuation byte `(b & 0xC0) == 0x80` at a strictly-interior
//! `0 < p < len`). This makes "every `str` is valid UTF-8" an ENFORCED invariant:
//! `substr` is the only public producer that could slice off-boundary. The
//! companion `s.is_char_boundary(i)` lets a tool check before slicing.
//!
//! Trap detection is RIGOROUS, not vacuous: `substr_traps` runs a substr whose
//! tool returns a POSITIVE value, so a CLEAN run is `Ok` and only a genuine wasm
//! trap is `Err(Trapped)` (a `return 0 - x` body would itself look "trapped" via
//! the negative-sentinel convention, hiding a missing trap).
//!
//! Bytes: "café" = c(0x63) a(0x61) f(0x66) é(0xC3 0xA9), len 5 — index 4 is the
//! lone continuation byte. "€abc" = €(0xE2 0x82 0xAC) a b c, len 6 — indices 1,2
//! are continuation bytes (a 3-byte head).

mod common;

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// Run a `0 - value` tool body and recover `value` from the negative sentinel.
/// Panics if the program genuinely TRAPPED (the message lacks the sentinel
/// prefix) — so a clean test is also a "did NOT trap" assertion.
use common::run_returning_negative as run_neg;

fn neg(body: &str) -> i64 {
    run_neg(&tool(body))
}

/// True iff `("<lit>").substr(a, b)` GENUINELY traps. The tool returns a POSITIVE
/// value (`v.len() + 1`), so a clean substr is `Ok` and only a real wasm trap is
/// `Err(Trapped)` — distinguishing a codepoint trap from a sentinel return.
fn substr_traps(lit: &str, a: i64, b: i64) -> bool {
    let src = tool(&format!(
        "    let s: str = \"{lit}\";\n    let v: str = s.substr({a}, {b});\n    return v.len() + 1;"
    ));
    let result = compile_tool(&src).expect("tool should compile");
    matches!(
        execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()),
        Err(ToolError::Trapped { .. })
    )
}

// ── mid-codepoint slices TRAP (rigorous: positive-return detector) ───────────

#[test]
fn substr_end_on_continuation_byte_traps() {
    // "café".substr(0,4): end=4 lands on 0xA9 (continuation) → trap.
    assert!(substr_traps("café", 0, 4));
}

#[test]
fn substr_start_on_continuation_byte_traps() {
    // "café".substr(4,5): start=4 lands on 0xA9 → trap.
    assert!(substr_traps("café", 4, 5));
}

#[test]
fn substr_three_byte_interior_traps() {
    // "€abc": both continuation bytes of the 3-byte € (indices 1,2) trap.
    assert!(substr_traps("€abc", 0, 1)); // end on 0x82
    assert!(substr_traps("€abc", 2, 4)); // start on 0xAC
    assert!(substr_traps("€abc", 1, 3)); // start on 0x82
}

// ── valid-boundary slices are CLEAN (rigorous: run_neg parses a real value) ───

#[test]
fn substr_at_codepoint_boundaries_is_clean() {
    // "café".substr(3, 5) == "é" (start=3 on the 0xC3 lead, end=5==len).
    let body = "    let s: str = \"café\";\n\
        \x20   let v: str = s.substr(3, 5);\n\
        \x20   return 0 - (v.byte_at(0) * 1000 + v.len());";
    assert_eq!(neg(body), 195002); // 0xC3=195, len 2
    assert!(!substr_traps("café", 3, 5));
}

#[test]
fn substr_ascii_prefix_is_clean() {
    // "€abc".substr(0, 3) == "€" (end=3 on 'a', a boundary) — the oracle's p=3.
    let body = "    let s: str = \"€abc\";\n\
        \x20   let v: str = s.substr(0, 3);\n\
        \x20   return 0 - (v.byte_at(0) * 1000 + v.len());";
    assert_eq!(neg(body), 226003); // 0xE2=226, len 3
    assert!(!substr_traps("€abc", 0, 3));
}

// ── ET-1: empty / end-of-string edges are CLEAN and deterministic ────────────

#[test]
fn substr_empty_at_end_is_clean() {
    // substr(len,len): start==end==len; the boundary load must NOT read
    // data_ptr+len. Checked twice (determinism).
    assert!(!substr_traps("café", 5, 5));
    assert!(!substr_traps("café", 5, 5));
    assert_eq!(
        neg(
            "    let s: str = \"café\";\n    let v: str = s.substr(5, 5);\n    return 0 - (v.len() + 7);"
        ),
        7
    );
}

#[test]
fn substr_empty_string_is_clean() {
    // substr(0,0) on "" (len==0): no readable byte; must not OOB. Twice.
    assert!(!substr_traps("", 0, 0));
    assert!(!substr_traps("", 0, 0));
    assert_eq!(
        neg(
            "    let s: str = \"\";\n    let v: str = s.substr(0, 0);\n    return 0 - (v.len() + 7);"
        ),
        7
    );
}

#[test]
fn substr_whole_multibyte_is_clean() {
    assert!(!substr_traps("café", 0, 5));
    assert!(!substr_traps("€abc", 0, 6));
}

// ── is_char_boundary (the rail) ──────────────────────────────────────────────

/// Run `("<lit>").is_char_boundary(<i_expr>)` and decode the bool from the
/// negative sentinel (`true` → -1 → 1, `false` → -2 → 2).
fn is_boundary(lit: &str, i_expr: &str) -> bool {
    let body = format!(
        "    let s: str = \"{lit}\";\n\
         \x20   if s.is_char_boundary({i_expr}) {{ return 0 - 1; }} else {{ return 0 - 2; }}"
    );
    match neg(&body) {
        1 => true,
        2 => false,
        other => panic!("unexpected is_char_boundary sentinel: {other}"),
    }
}

#[test]
fn is_char_boundary_basic() {
    // "€abc" len 6. Boundaries: 0,3,4,5,6; interior continuation bytes: 1,2.
    assert!(is_boundary("€abc", "0"));
    assert!(!is_boundary("€abc", "1"));
    assert!(!is_boundary("€abc", "2"));
    assert!(is_boundary("€abc", "3"));
    assert!(is_boundary("€abc", "6")); // len
    assert!(!is_boundary("€abc", "7")); // > len
    assert!(!is_boundary("€abc", "0 - 1")); // < 0
}

// ── ET-2: the rail and the floor agree on EVERY position ─────────────────────

#[test]
fn is_char_boundary_matches_substr_trap_oracle() {
    // The single-predicate gate: for every p ∈ [0, len], `is_char_boundary(p)`
    // must equal `!(substr(0, p) traps)`. One disagreement = the rail lies about
    // the floor. (Uses the rigorous positive-return trap detector.)
    let lit = "€abc"; // len 6, interior at 1,2
    for p in 0..=6 {
        let rail = is_boundary(lit, &p.to_string());
        let floor_traps = substr_traps(lit, 0, p);
        assert_eq!(
            rail, !floor_traps,
            "position {p}: is_char_boundary={rail} but substr(0,{p}) traps={floor_traps}"
        );
    }
}

// ── ET-4: split_on / trim of multibyte content never trips the trap ──────────

#[test]
fn split_on_multibyte_delimiter_is_clean() {
    // The adversarial case: a MULTI-BYTE delimiter. "a€b€c".split_on("€") →
    // ["a","b","c"], sliced at delimiter (codepoint) boundaries. An off-by-one in
    // str_split_on would slice off-boundary → the substr trap fires → this reds.
    let body = "    let s: str = \"a€b€c\";\n\
        \x20   let parts: Vec<str> = s.split_on(\"€\");\n\
        \x20   let n: i64 = parts.len();\n\
        \x20   let seg: str = parts.get(1);\n\
        \x20   return 0 - (n * 1000 + seg.byte_at(0));";
    assert_eq!(neg(body), 3098); // 3 segments, seg[1]=="b" (98)
}

#[test]
fn trim_around_multibyte_is_clean() {
    // trim strips ASCII whitespace (boundaries) around multibyte content.
    // "  é  ".trim() == "é" (0xC3 0xA9), never slicing the codepoint.
    let body = "    let s: str = \"  é  \";\n\
        \x20   let t: str = s.trim();\n\
        \x20   return 0 - (t.len() * 1000 + t.byte_at(0));";
    assert_eq!(neg(body), 2195); // "é": len 2, byte0=0xC3=195
}
