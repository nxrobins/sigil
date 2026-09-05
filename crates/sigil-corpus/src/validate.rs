//! The validation gate — the corpus's oracle (`docs/specs/training-corpus.md`
//! §4). Every positive must compile clean through the real compiler; every
//! negative must reproduce its declared diagnostic code. Failures are returned
//! as a `reject` reason (drop + count); invariant breaches panic.

use std::sync::mpsc;
use std::thread;
use std::time::Duration;

use sigil_compiler::Severity;
use sigil_compiler::compiler::compile_named_module;
use sigil_compiler::registry::CODES;

use crate::schema::{VALIDATE_BUDGET_MS, Validated, ValidationKind};

/// What the compiler said about a candidate, within budget.
enum Outcome {
    /// Compiled clean (parse → name-res → type-check → AIR → wasm).
    Clean,
    /// Failed with these error-severity diagnostic codes.
    Errors(Vec<String>),
}

/// Run the full compiler within `VALIDATE_BUDGET_MS`. Returns `None` on timeout
/// — the worker thread is abandoned (the process exits soon after a build), so
/// a pathological input can never hang the whole run (ET-C1).
fn compile_within_budget(name: String, src: String) -> Option<Outcome> {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let outcome = match compile_named_module(name, src) {
            Ok(_) => Outcome::Clean,
            Err(e) => Outcome::Errors(
                e.into_diagnostics()
                    .iter()
                    .filter(|d| d.severity() == Severity::Error)
                    .map(|d| d.code().as_str().to_string())
                    .collect(),
            ),
        };
        let _ = tx.send(outcome);
    });
    rx.recv_timeout(Duration::from_millis(VALIDATE_BUDGET_MS))
        .ok()
}

/// A positive example must compile clean. `Err(reason)` → drop + count.
pub fn certify_positive(name: &str, src: &str) -> Result<Validated, String> {
    match compile_within_budget(name.to_string(), src.to_string()) {
        None => Err("VALIDATE_TIMEOUT".to_string()),
        Some(Outcome::Clean) => Ok(Validated {
            ok: true,
            how: ValidationKind::ParsedTypechecked,
        }),
        Some(Outcome::Errors(codes)) => Err(format!(
            "POSITIVE_DID_NOT_COMPILE:observed={}",
            join(&codes)
        )),
    }
}

/// A negative example must reproduce its declared `code`. An unknown/malformed
/// code is a pipeline bug and panics (ET-C2: `CORPUS_UNKNOWN_CODE`); a valid
/// code the compiler does not reproduce is a drop + count.
pub fn certify_negative(name: &str, src: &str, expected: &str) -> Result<Validated, String> {
    if !is_registry_code(expected) {
        panic!("CORPUS_UNKNOWN_CODE: `{expected}` is not a registered diagnostic code");
    }
    match compile_within_budget(name.to_string(), src.to_string()) {
        None => Err("VALIDATE_TIMEOUT".to_string()),
        Some(Outcome::Clean) => Err(format!(
            "CODE_NOT_REPRODUCED:expected={expected},observed=<none>"
        )),
        Some(Outcome::Errors(codes)) => {
            if codes.iter().any(|c| c == expected) {
                Ok(Validated {
                    ok: true,
                    how: ValidationKind::ReproducedCode {
                        code: expected.to_string(),
                    },
                })
            } else {
                Err(format!(
                    "CODE_NOT_REPRODUCED:expected={expected},observed={}",
                    join(&codes)
                ))
            }
        }
    }
}

/// Validate a whole compilation UNIT (a stdlib file standalone, or the inlined
/// selfhost trio) within budget. `Ok(())` = compiled clean; `Err(reason)` is a
/// counted drop reason shared by every record the unit witnesses. The caller
/// memoizes by unit key so each file/trio compiles once.
pub fn validate_unit(name: &str, src: &str) -> Result<(), String> {
    match compile_within_budget(name.to_string(), src.to_string()) {
        None => Err("VALIDATE_TIMEOUT".to_string()),
        Some(Outcome::Clean) => Ok(()),
        Some(Outcome::Errors(codes)) => {
            Err(format!("FILE_DID_NOT_COMPILE:observed={}", join(&codes)))
        }
    }
}

/// How a standalone fixture compiled. The registry-filtered codes drive the
/// derived negative's `code` (ET-C2 — derived from the compiler, never the
/// fixture header).
pub enum FixtureVerdict {
    Clean,
    Errored(Vec<String>),
    Timeout,
}

pub fn classify_fixture(name: &str, src: &str) -> FixtureVerdict {
    match compile_within_budget(name.to_string(), src.to_string()) {
        None => FixtureVerdict::Timeout,
        Some(Outcome::Clean) => FixtureVerdict::Clean,
        Some(Outcome::Errors(codes)) => {
            FixtureVerdict::Errored(codes.into_iter().filter(|c| is_registry_code(c)).collect())
        }
    }
}

/// `^[A-Z][0-9]{3}$` AND present in the compiler's registry (ET-C2).
pub fn is_registry_code(code: &str) -> bool {
    is_well_formed_code(code) && CODES.iter().any(|e| e.code.as_str() == code)
}

/// The `^[A-Z][0-9]{3}$` shape every diagnostic code has.
pub fn is_well_formed_code(code: &str) -> bool {
    let b = code.as_bytes();
    b.len() == 4 && b[0].is_ascii_uppercase() && b[1..].iter().all(u8::is_ascii_digit)
}

fn join(codes: &[String]) -> String {
    if codes.is_empty() {
        "<none>".to_string()
    } else {
        codes.join("|")
    }
}

// ── §9 ET-C4: secret / PII scan ───────────────────────────────────────────────

/// Scan one field for a secret/PII pattern; returns the matched pattern name.
/// Conservative by construction: the email check requires an alphanumeric byte
/// immediately before `@`, so SIGIL annotations (`@Mut`, `@in`, `@ReadOnly`,
/// always preceded by space/backtick) never match.
pub fn find_secret(text: &str) -> Option<&'static str> {
    if text.contains("PRIVATE KEY") {
        return Some("pem-private-key");
    }
    if has_aws_key(text) {
        return Some("aws-access-key");
    }
    if has_email(text) {
        return Some("email");
    }
    if has_hex_run(text, 32) {
        return Some("long-hex-token");
    }
    None
}

fn has_aws_key(text: &str) -> bool {
    let bytes = text.as_bytes();
    bytes.windows(4).enumerate().any(|(i, w)| {
        w == b"AKIA"
            && bytes.get(i + 4..i + 20).is_some_and(|tail| {
                tail.iter()
                    .all(|b| b.is_ascii_uppercase() || b.is_ascii_digit())
            })
    })
}

fn has_email(text: &str) -> bool {
    let bytes = text.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        if b == b'@'
            && i > 0
            && bytes[i - 1].is_ascii_alphanumeric()
            && let Some(rest) = text.get(i + 1..)
            && looks_like_domain(rest)
        {
            return true;
        }
    }
    false
}

/// `<alnum/-/.>* . <alpha>{2,}` — at least one dot and a 2+-letter final label.
fn looks_like_domain(s: &str) -> bool {
    let mut saw_dot = false;
    let mut final_label_alpha = 0usize;
    for &b in s.as_bytes() {
        if b == b'.' {
            saw_dot = true;
            final_label_alpha = 0;
        } else if b.is_ascii_alphabetic() {
            final_label_alpha += 1;
        } else if b.is_ascii_digit() || b == b'-' {
            final_label_alpha = 0;
        } else {
            break;
        }
    }
    saw_dot && final_label_alpha >= 2
}

/// Detect a `long-hex-token` credential (API key / key material / hash): a run of
/// `>= min` hex digits that is actually hexadecimal and is not a SIGIL numeric
/// literal. Two refinements keep legitimate integer literals (u256/Solidity:
/// 78-digit decimals, `0x` addresses/hashes) from false-positive flagging. First,
/// the run must contain a hex LETTER (`a-f`/`A-F`) — a pure-decimal run is a
/// decimal integer literal, never a hex credential. Second, the run must not be
/// the digits of a `0x`/`0X` integer literal. A bare mixed-hex token in prose or a
/// string literal (e.g. a pasted key without `0x`) still matches.
fn has_hex_run(text: &str, min: usize) -> bool {
    let bytes = text.as_bytes();
    let mut run_start = 0usize;
    let mut run = 0usize;
    let mut saw_hex_letter = false;
    for (i, &b) in bytes.iter().enumerate() {
        if b.is_ascii_hexdigit() {
            if run == 0 {
                run_start = i;
                saw_hex_letter = false;
            }
            run += 1;
            if b.is_ascii_alphabetic() {
                saw_hex_letter = true;
            }
            if run >= min && saw_hex_letter && !is_hex_literal_digits(bytes, run_start) {
                return true;
            }
        } else {
            run = 0;
        }
    }
    false
}

/// True when the hex-digit run starting at `run_start` is the body of a SIGIL
/// `0x`/`0X` integer literal — immediately preceded by `0x`. (The `x` is not a
/// hex digit, so it ends the preceding run; the literal's digits form a fresh run
/// beginning right after it.) Such a run is a numeric literal, not a credential.
fn is_hex_literal_digits(bytes: &[u8], run_start: usize) -> bool {
    run_start >= 2 && matches!(bytes[run_start - 1], b'x' | b'X') && bytes[run_start - 2] == b'0'
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn well_formed_codes() {
        assert!(is_well_formed_code("T215"));
        assert!(is_well_formed_code("P001"));
        assert!(!is_well_formed_code("t215"));
        assert!(!is_well_formed_code("T21"));
        assert!(!is_well_formed_code("TT15"));
    }

    #[test]
    fn registry_membership() {
        assert!(is_registry_code("P001"));
        assert!(!is_registry_code("Z999"));
    }

    #[test]
    fn positive_compiles_and_negative_reproduces() {
        let good = "module demo; pub fn f() -> i64 { return 1; }";
        assert!(certify_positive("demo", good).is_ok());

        // A real type error: returning bool from an i64 function.
        let bad = "module demo; pub fn f() -> i64 { return true; }";
        // Discover the code the compiler actually emits, then confirm the gate
        // reproduces it and rejects a wrong-but-valid code.
        let outcome = compile_within_budget("demo".to_string(), bad.to_string());
        let codes = match outcome {
            Some(Outcome::Errors(c)) => c,
            _ => panic!("expected the bad program to error"),
        };
        let real = codes
            .iter()
            .find(|c| is_registry_code(c))
            .expect("a registry code");
        assert!(certify_negative("demo", bad, real).is_ok());
        // P001 (a parser code) is valid but not what this program emits.
        assert!(certify_negative("demo", bad, "P001").is_err());
    }

    #[test]
    fn secret_scan_flags_and_spares() {
        assert_eq!(find_secret("contact user@example.com"), Some("email"));
        assert_eq!(
            find_secret("-----BEGIN RSA PRIVATE KEY-----"),
            Some("pem-private-key")
        );
        assert_eq!(
            find_secret("key AKIAIOSFODNN7EXAMPLE here"),
            Some("aws-access-key")
        );
        // SIGIL annotations and ordinary prose are NOT secrets.
        assert_eq!(find_secret("a mutable `@Mut` borrow `@in r`"), None);
        assert_eq!(find_secret("see the @ReadOnly view"), None);
        assert_eq!(find_secret("Mutable reference escapes its region"), None);
    }

    #[test]
    fn long_hex_heuristic_spares_numeric_literals() {
        // A real bare hexadecimal credential (mixed hex, no `0x`) IS flagged.
        assert_eq!(
            find_secret("token deadbeefcafedeadbeefcafedeadbeef01 here"),
            Some("long-hex-token")
        );
        // u256/Solidity numeric literals are NOT credentials:
        // (a) a wide DECIMAL literal (pure digits, no hex letter) — e.g. 2^256-1.
        assert_eq!(
            find_secret(
                "let x: u256 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;"
            ),
            None
        );
        // (b) a `0x` HEX integer literal (Solidity address / 256-bit hash / max u256).
        assert_eq!(
            find_secret(
                "let m: u256 = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;"
            ),
            None
        );
        assert_eq!(
            find_secret("address a = 0xAbC0000000000000000000000000000000000123;"),
            None
        );
    }

    #[test]
    fn selfhost_trio_completes_within_validation_budget() {
        let lexer =
            include_str!("../../../selfhost/lexer.sigil").replace("\nmodule lexer;\n", "\n");
        let parser =
            include_str!("../../../selfhost/parser.sigil").replace("\nmodule parser;\n", "\n");
        let typecheck = include_str!("../../../selfhost/typecheck.sigil")
            .replace("\nmodule typecheck;\n", "\n");
        let unit = format!("module tool;\n{lexer}\n{parser}\n{typecheck}\n");

        assert_eq!(
            validate_unit("selfhost-trio-budget-canary", &unit),
            Ok(()),
            "the fixed corpus validation budget must retain self-host source evidence"
        );
    }
}
