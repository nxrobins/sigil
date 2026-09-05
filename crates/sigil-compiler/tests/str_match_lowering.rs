//! String-literal match arms allocate NO pattern header.
//!
//! Under the data-ptr comparison the lowering materialized each arm's
//! pattern as a real 8-byte str header — `BumpAlloc` + two `StoreField`s —
//! purely so the comparison could take two headers. With byte comparison
//! (`AirStmt::StrBytesEq`, PR #699) the pattern side needs no header at
//! all: its data pointer is the interned literal (`AirValue::StrLit`) and
//! its length is a compile-time constant. Only the scrutinee — which may
//! be a view or a constructed str — is read from a header.
//!
//! Dropping the header removes one allocation (and its alloc-fuel charge,
//! and — inside an actor with state — a persistent allocation) per string
//! arm per execution. This test pins the shape so the header cannot quietly
//! come back.

use sigil_compiler::air::AirStmt;
use sigil_compiler::compile_module;

/// Count `BumpAlloc` statements in the one function whose name contains
/// `needle`, panicking if no function matches (so a mangling change cannot
/// turn the assertion vacuous).
fn bump_allocs_in(src: &str, needle: &str) -> usize {
    let compiled = compile_module(src).expect("fixture must compile");
    let matching: Vec<_> = compiled
        .air
        .functions
        .iter()
        .filter(|f| f.name.contains(needle))
        .collect();
    assert!(
        !matching.is_empty(),
        "no AIR function named like {needle:?}; fixture or mangling changed"
    );
    matching
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.stmts.iter())
        .filter(|s| matches!(s, AirStmt::BumpAlloc { .. }))
        .count()
}

/// The probe takes its scrutinee as a PARAMETER so the match arms are the
/// only conceivable allocation sites in the function body.
const MATCH_PROBE: &str = r#"module m;
pub fn match_probe(s: str) -> i64 {
    match s {
        "ab" => { return 1; },
        "cd" => { return 2; },
        _ => { return 0; },
    }
}
"#;

#[test]
fn string_literal_match_arms_allocate_no_pattern_headers() {
    assert_eq!(
        bump_allocs_in(MATCH_PROBE, "match_probe"),
        0,
        "a string-literal match arm must not BumpAlloc a pattern header \
         (the pattern's data is `StrLit` and its length is compile-time)"
    );
}

/// Anti-stub: the counter must SEE a header allocation where one genuinely
/// exists — a str literal in EXPRESSION position materializes its fat-pointer
/// header on the heap. If this fails, the zero above proves nothing.
const LITERAL_PROBE: &str = r#"module m;
pub fn literal_probe() -> i64 {
    let t: str = "zz";
    return t.len();
}
"#;

#[test]
fn the_alloc_counter_sees_expression_position_headers() {
    assert!(
        bump_allocs_in(LITERAL_PROBE, "literal_probe") >= 1,
        "an expression-position str literal allocates its header; \
         a zero here would make the match-arm assertion vacuous"
    );
}
