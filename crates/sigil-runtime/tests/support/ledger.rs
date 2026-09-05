//! Extractors shared by the claims ledgers' tests: the public ledger (`docs/CLAIMS.md`, checked
//! by `claims_ledger.rs`) and the research overlay's ledger (`proofs/lean-research/CLAIMS.md`,
//! checked by `research_claims_ledger.rs`). Both ledgers carry the same machine-checkable tags,
//! so both must be read by the same code: a divergence here would let one ledger drift in a way
//! the other's checks could not see. SC-P4: `claims_ledger.rs` proves every extractor non-vacuous.
//!
//! `allow(dead_code)`: this module is included by `#[path]` into several test binaries, each of
//! which uses a different subset, and CI builds with `-D warnings`.

use std::collections::HashMap;

/// Pull every `@test:<name>` tag out of a ledger.
#[allow(dead_code)]
pub fn ledger_test_tags(src: &str) -> Vec<String> {
    let mut out = Vec::new();
    for (i, _) in src.match_indices("@test:") {
        let rest = &src[i + 6..];
        let end = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .unwrap_or(rest.len());
        if end > 0 {
            out.push(rest[..end].to_string());
        }
    }
    out
}

/// Pull every `@thm:<Name>` tag out of a ledger. Names are manifest-relative (`Chk.sound`,
/// not `LambdaSigil.Chk.sound`), matching an `axiom-targets.txt` exactly.
///
/// `.` is both a name separator and sentence punctuation, so a tag ending a sentence
/// (`@thm:Chk.sound.`) would otherwise capture the full stop. Trailing dots are stripped —
/// no Lean declaration name ends in one.
#[allow(dead_code)]
pub fn ledger_thm_tags(src: &str) -> Vec<String> {
    let mut out = Vec::new();
    for (i, _) in src.match_indices("@thm:") {
        let rest = &src[i + 5..];
        let end = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '.'))
            .unwrap_or(rest.len());
        let name = rest[..end].trim_end_matches('.');
        if !name.is_empty() {
            out.push(name.to_string());
        }
    }
    out
}

/// Pull `NAME = VALUE` pairs out of the fenced ```pins block(s).
#[allow(dead_code)]
pub fn ledger_pins(src: &str) -> HashMap<String, u64> {
    let mut out = HashMap::new();
    let mut rest = src;
    while let Some(start) = rest.find("```pins") {
        let body = &rest[start + 7..];
        let Some(end) = body.find("```") else { break };
        for line in body[..end].lines() {
            let line = line.trim();
            let Some((k, v)) = line.split_once('=') else {
                continue;
            };
            let k = k.trim();
            let v = v.trim().replace('_', "");
            if k.is_empty() || v.is_empty() || !v.chars().all(|c| c.is_ascii_digit()) {
                continue;
            }
            if let Ok(n) = v.parse::<u64>() {
                out.insert(k.to_string(), n);
            }
        }
        rest = &body[end..];
    }
    out
}

/// Pull the numbered claims from section B. Claim numbers are stable references,
/// so duplicates or gaps make the ledger ambiguous even when Markdown renders.
#[allow(dead_code)]
pub fn ledger_claim_numbers(src: &str) -> Vec<usize> {
    let Some(section) = src.split_once("## §B").map(|(_, rest)| rest) else {
        return Vec::new();
    };
    let section = section.split("\n---\n").next().unwrap_or(section);
    section
        .lines()
        .filter_map(|line| {
            let (number, claim) = line.split_once(". ")?;
            if !claim.starts_with("**") {
                return None;
            }
            number.parse().ok()
        })
        .collect()
}

/// Find `NAME: usize = 1_234;` in Rust source and return the numeric value.
#[allow(dead_code)]
pub fn rust_const_value(src: &str, name: &str) -> Option<u64> {
    let needle = format!("{name}: usize = ");
    let i = src.find(&needle)?;
    let rest = &src[i + needle.len()..];
    let end = rest.find(';')?;
    let digits: String = rest[..end].chars().filter(|c| c.is_ascii_digit()).collect();
    digits.parse::<u64>().ok()
}
