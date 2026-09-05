//! Axis-6 (stability contract): golden snapshot of the diagnostic code list.
//!
//! `registry::CODES` is SIGIL's public errors-as-API surface. Codes are
//! promised to be stable — never silently renamed, removed, or repurposed
//! (docs/ERROR-CODES.md). Before this test that promise had ZERO automated
//! enforcement; a rename or removal would pass CI unnoticed.
//!
//! This pins the full (code, title) set to a committed golden file
//! (`tests/golden/diagnostic_code_list.txt`). Any add / remove / retitle makes
//! `diagnostic_code_list_matches_golden` fail, forcing the change to be
//! deliberate: regenerate with
//! `SIGIL_REGEN_CODE_SNAPSHOT=1 cargo test -p sigil-compiler --test diagnostic_code_list_snapshot`
//! and, for a removal or rename, record the deprecation per the stability
//! contract. `snapshot_guard_detects_drift` proves the comparison has teeth.

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use sigil_compiler::diagnostics::registry;

fn golden_path() -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.push("tests/golden/diagnostic_code_list.txt");
    p
}

/// Serialize the live registry as sorted `CODE\tTITLE` lines.
fn current_snapshot() -> String {
    let mut rows: Vec<(&str, &str)> = registry::CODES
        .iter()
        .map(|e| (e.code.as_str(), e.title))
        .collect();
    rows.sort_unstable();
    let mut out = String::new();
    for (code, title) in rows {
        out.push_str(code);
        out.push('\t');
        out.push_str(title);
        out.push('\n');
    }
    out
}

/// Drift between a golden snapshot and the current one. One human-readable line
/// per added / removed / retitled code; empty == identical.
fn drift(golden: &str, current: &str) -> Vec<String> {
    fn parse(s: &str) -> BTreeMap<&str, &str> {
        s.lines()
            .filter(|l| !l.trim().is_empty())
            .filter_map(|l| l.split_once('\t'))
            .collect()
    }
    let golden = parse(golden);
    let current = parse(current);
    let mut out = Vec::new();
    for (code, title) in &current {
        match golden.get(code) {
            None => out.push(format!("ADDED {code} ({title})")),
            Some(prev) if prev != title => {
                out.push(format!("RETITLED {code}: `{prev}` -> `{title}`"));
            }
            Some(_) => {}
        }
    }
    for code in golden.keys() {
        if !current.contains_key(code) {
            out.push(format!("REMOVED {code}"));
        }
    }
    out.sort();
    out
}

#[test]
fn diagnostic_code_list_matches_golden() {
    let current = current_snapshot();
    if std::env::var_os("SIGIL_REGEN_CODE_SNAPSHOT").is_some() {
        let path = golden_path();
        fs::create_dir_all(path.parent().expect("golden path has a parent"))
            .expect("create golden dir");
        fs::write(&path, current.as_bytes()).expect("write golden snapshot");
        return;
    }
    let golden = fs::read_to_string(golden_path()).unwrap_or_else(|e| {
        panic!(
            "missing golden snapshot at {} ({e}); regenerate with \
             SIGIL_REGEN_CODE_SNAPSHOT=1 cargo test -p sigil-compiler \
             --test diagnostic_code_list_snapshot",
            golden_path().display()
        )
    });
    let drifted = drift(&golden, &current);
    assert!(
        drifted.is_empty(),
        "diagnostic code list drifted from the golden snapshot:\n  {}\n\n\
         If intentional, regenerate with SIGIL_REGEN_CODE_SNAPSHOT=1 (and record \
         any removal/rename as a deprecation per the stability contract).",
        drifted.join("\n  ")
    );
}

#[test]
fn snapshot_guard_detects_drift() {
    // The guard must report a retitle, a removal, and an addition.
    let golden = "T001\tType mismatch\nT002\tOld title\nZ999\tGone code\n";
    let current = "T001\tType mismatch\nT002\tNew title\nT003\tBrand new\n";
    let drifted = drift(golden, current);
    assert!(
        drifted.iter().any(|s| s.starts_with("RETITLED T002")),
        "{drifted:?}"
    );
    assert!(drifted.iter().any(|s| s == "REMOVED Z999"), "{drifted:?}");
    assert!(
        drifted.iter().any(|s| s.starts_with("ADDED T003")),
        "{drifted:?}"
    );
    assert_eq!(drifted.len(), 3, "unexpected drift entries: {drifted:?}");
}

#[test]
fn snapshot_guard_is_silent_on_identical() {
    let snap = current_snapshot();
    assert!(drift(&snap, &snap).is_empty());
}
