//! SOL-XFILE PR1/L1 — the multi-file PROJECT resolver: closure resolution over an
//! in-memory file-set (imports are MAP LOOKUPS, never filesystem reads), the entry-main
//! rule, the per-file pragma gate, and the dumb closure bounds. Every reject asserts its
//! exact FE code (fail-closed, never best-effort).
//! PR2/L2 extends the accepted base kinds across files: an ABSTRACT base contributes its
//! members, an INTERFACE base contributes nothing, a LIBRARY base stays FE476.

use std::collections::BTreeMap;

use sigil_frontends::translate_solidity_project;

fn map(entries: &[(&str, &str)]) -> BTreeMap<String, String> {
    entries
        .iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect()
}

/// First diagnostic code of a rejected project translate (panics on accept — used only
/// where the fixture MUST reject).
fn reject_code(files: &BTreeMap<String, String>, entry: &str) -> String {
    match translate_solidity_project(files, entry) {
        Ok(_) => panic!("expected a reject for entry `{entry}`, but it translated"),
        Err(diags) => diags[0].code.to_string(),
    }
}

const PRAGMA: &str = "pragma solidity ^0.8.20;\n";

// ── accept: cross-file CONCRETE inheritance ─────────────────────────────────────────

#[test]
fn project_two_file_concrete_base_translates() {
    let files = map(&[
        (
            "token/Token.sol",
            "pragma solidity ^0.8.20;\nimport {Base} from \"../lib/Base.sol\";\ncontract Token is Base {\n    function bump(uint256 v) public { total = total + v; }\n}\n",
        ),
        (
            "lib/Base.sol",
            "pragma solidity ^0.8.20;\ncontract Base {\n    uint256 total;\n    function get() public view returns (uint256) { return total; }\n}\n",
        ),
    ]);
    let out = translate_solidity_project(&files, "token/Token.sol").expect("translates");
    // The union merged the base's state + fn into the entry's contract.
    assert!(
        out.text.contains("record Token"),
        "flattened main is Token:\n{}",
        out.text
    );
    assert!(
        out.text.contains("total"),
        "base state merged:\n{}",
        out.text
    );
    assert!(out.text.contains("fn get"), "base fn merged:\n{}", out.text);
}

#[test]
fn project_abstract_base_across_files_contributes_members() {
    // PR2/L2: the real OZ shape (minus the base-ctor wall, which is PR4) — a concrete entry
    // inherits an ABSTRACT base from another file that itself inherits an INTERFACE. The
    // abstract's members flatten into the entry; the interface contributes nothing.
    let files = map(&[
        (
            "Token.sol",
            "pragma solidity ^0.8.20;\nimport {Ledger} from \"./base/Ledger.sol\";\ncontract Token is Ledger {\n    function bump(uint256 v) public { total = total + v; }\n}\n",
        ),
        (
            "base/Ledger.sol",
            "pragma solidity ^0.8.20;\nimport {ILedger} from \"./ILedger.sol\";\nabstract contract Ledger is ILedger {\n    uint256 total;\n    function get() public view returns (uint256) { return total; }\n}\n",
        ),
        (
            "base/ILedger.sol",
            "pragma solidity >=0.6.0;\ninterface ILedger { function get() external view returns (uint256); }\n",
        ),
    ]);
    let out = translate_solidity_project(&files, "Token.sol").expect("translates");
    assert!(
        out.text.contains("record Token"),
        "main is Token:\n{}",
        out.text
    );
    assert!(
        out.text.contains("total"),
        "abstract base state merged:\n{}",
        out.text
    );
    assert!(
        out.text.contains("fn get"),
        "abstract base fn merged:\n{}",
        out.text
    );
    assert!(
        out.text.contains("fn bump"),
        "entry's own fn present:\n{}",
        out.text
    );
}

#[test]
fn project_library_base_across_files_is_fe476() {
    let files = map(&[
        (
            "Main.sol",
            "pragma solidity ^0.8.20;\nimport {L} from \"./L.sol\";\ncontract Main is L { uint256 y; }\n",
        ),
        (
            "L.sol",
            "pragma solidity ^0.8.20;\nlibrary L { function h() internal pure returns (uint256) { return 1; } }\n",
        ),
    ]);
    assert_eq!(reject_code(&files, "Main.sol"), "FE476");
}

#[test]
fn project_named_and_plain_import_forms_resolve() {
    // `import "p";` and `import {A, B} from "p";` both carry exactly one path.
    let files = map(&[
        (
            "Main.sol",
            "pragma solidity ^0.8.20;\nimport \"./a/One.sol\";\nimport {Two} from \"./a/Two.sol\";\ncontract Main is One, Two { }\n",
        ),
        (
            "a/One.sol",
            "pragma solidity ^0.8.20;\ncontract One { uint256 x; }\n",
        ),
        (
            "a/Two.sol",
            "pragma solidity ^0.8.20;\ncontract Two { uint256 y; }\n",
        ),
    ]);
    let out = translate_solidity_project(&files, "Main.sol").expect("translates");
    assert!(out.text.contains("record Main"));
    assert!(out.text.contains('x') && out.text.contains('y'));
}

#[test]
fn project_diamond_closure_loads_once_and_import_cycles_are_harmless() {
    // A imports B and C; B and C both import D (the closure is a SET — D parses once).
    // B and C also import EACH OTHER (an import cycle, legal in Solidity) — harmless
    // because visited-set membership, not recursion, drives loading.
    let files = map(&[
        (
            "A.sol",
            "pragma solidity ^0.8.20;\nimport \"./B.sol\";\nimport \"./C.sol\";\ncontract A is B, C { }\n",
        ),
        (
            "B.sol",
            "pragma solidity ^0.8.20;\nimport \"./D.sol\";\nimport \"./C.sol\";\ncontract B is D { uint256 b; }\n",
        ),
        (
            "C.sol",
            "pragma solidity ^0.8.20;\nimport \"./D.sol\";\nimport \"./B.sol\";\ncontract C is D { uint256 c; }\n",
        ),
        (
            "D.sol",
            "pragma solidity ^0.8.20;\ncontract D { uint256 d; }\n",
        ),
    ]);
    let out = translate_solidity_project(&files, "A.sol").expect("translates");
    assert!(out.text.contains("record A"));
}

#[test]
fn project_interface_only_file_with_old_pragma_is_exempt() {
    // An interface-only closure file (the OZ `>=0.5/0.6` idiom) contributes no code and
    // is EXEMPT from the >=0.8 gate; the code-bearing entry still passes its own.
    let files = map(&[
        (
            "Main.sol",
            "pragma solidity ^0.8.20;\nimport {IThing} from \"./IThing.sol\";\ncontract Main { uint256 n; }\n",
        ),
        (
            "IThing.sol",
            "pragma solidity >=0.5.0;\ninterface IThing { function n() external view returns (uint256); }\n",
        ),
    ]);
    translate_solidity_project(&files, "Main.sol").expect("interface-only old pragma is exempt");
}

// ── rejects: resolution + bounds (each names its exact FE code) ─────────────────────

#[test]
fn project_missing_import_is_fe476() {
    let files = map(&[(
        "Main.sol",
        "pragma solidity ^0.8.20;\nimport \"./Gone.sol\";\ncontract Main { }\n",
    )]);
    assert_eq!(reject_code(&files, "Main.sol"), "FE476");
}

#[test]
fn project_root_escape_is_fe476() {
    // `../Outside.sol` from a root-level file normalizes PAST the root → rejected
    // before any lookup (the map could not contain it anyway — defense in depth).
    let files = map(&[(
        "Main.sol",
        "pragma solidity ^0.8.20;\nimport \"../Outside.sol\";\ncontract Main { }\n",
    )]);
    assert_eq!(reject_code(&files, "Main.sol"), "FE476");
}

#[test]
fn project_backslash_and_absolute_paths_are_fe476() {
    let files = map(&[
        (
            "A.sol",
            "pragma solidity ^0.8.20;\nimport \"a\\\\B.sol\";\ncontract A { }\n",
        ),
        (
            "B.sol",
            "pragma solidity ^0.8.20;\nimport \"/etc/passwd\";\ncontract B { }\n",
        ),
    ]);
    assert_eq!(reject_code(&files, "A.sol"), "FE476");
    assert_eq!(reject_code(&files, "B.sol"), "FE476");
}

#[test]
fn project_aliased_import_stays_fe476() {
    let files = map(&[
        (
            "Main.sol",
            "pragma solidity ^0.8.20;\nimport {One as Uno} from \"./One.sol\";\ncontract Main { }\n",
        ),
        ("One.sol", "pragma solidity ^0.8.20;\ncontract One { }\n"),
    ]);
    assert_eq!(reject_code(&files, "Main.sol"), "FE476");
}

#[test]
fn project_cross_file_duplicate_contract_name_is_fe420() {
    let files = map(&[
        (
            "Main.sol",
            "pragma solidity ^0.8.20;\nimport \"./A.sol\";\nimport \"./B.sol\";\ncontract Main { }\n",
        ),
        (
            "A.sol",
            "pragma solidity ^0.8.20;\ncontract Twin { uint256 a; }\n",
        ),
        (
            "B.sol",
            "pragma solidity ^0.8.20;\ncontract Twin { uint256 b; }\n",
        ),
    ]);
    assert_eq!(reject_code(&files, "Main.sol"), "FE420");
}

#[test]
fn project_entry_zero_or_two_concrete_is_fe470() {
    // Zero concrete contracts in the ENTRY file.
    let files0 = map(&[(
        "Main.sol",
        "pragma solidity ^0.8.20;\ninterface IOnly { }\n",
    )]);
    assert_eq!(reject_code(&files0, "Main.sol"), "FE470");
    // Two concrete contracts in the ENTRY file (the entry must name exactly one).
    let files2 = map(&[(
        "Main.sol",
        "pragma solidity ^0.8.20;\ncontract A { }\ncontract B { }\n",
    )]);
    assert_eq!(reject_code(&files2, "Main.sol"), "FE470");
}

#[test]
fn project_imported_concrete_cannot_steal_main() {
    // ENTRY-MAIN RULE (EX-1/MC-1): an imported file's concrete contract that DERIVES the
    // entry's contract must not become main (union-wide sink analysis would pick it —
    // translating a different artifact than the user named). The main stays `Token`.
    let files = map(&[
        (
            "Token.sol",
            "pragma solidity ^0.8.20;\nimport \"./Mock.sol\";\ncontract Token { uint256 supply; }\n",
        ),
        (
            "Mock.sol",
            "pragma solidity ^0.8.20;\nimport \"./Token.sol\";\ncontract TokenMock is Token { uint256 extra; }\n",
        ),
    ]);
    let out = translate_solidity_project(&files, "Token.sol").expect("translates");
    assert!(
        out.text.contains("record Token") && !out.text.contains("record TokenMock"),
        "main is the ENTRY's contract, never an imported deriver:\n{}",
        out.text
    );
}

#[test]
fn project_code_bearing_old_pragma_file_is_fe411() {
    // A CONCRETE-contract file with a pre-0.8 pragma smuggles wrapping semantics → FE411
    // naming the file (the interface exemption must not leak to code-bearing files).
    let files = map(&[
        (
            "Main.sol",
            "pragma solidity ^0.8.20;\nimport {Old} from \"./Old.sol\";\ncontract Main is Old { }\n",
        ),
        (
            "Old.sol",
            "pragma solidity ^0.7.0;\ncontract Old { uint256 o; }\n",
        ),
    ]);
    let diags = match translate_solidity_project(&files, "Main.sol") {
        Ok(_) => panic!("old code-bearing pragma must reject"),
        Err(d) => d,
    };
    assert_eq!(diags[0].code, "FE411");
    assert!(
        diags[0].message.contains("Old.sol"),
        "names the file: {}",
        diags[0].message
    );
}

#[test]
fn project_import_depth_over_16_is_fe402() {
    // A 20-deep linear import chain (no inheritance — pure closure depth).
    let mut entries: Vec<(String, String)> = Vec::new();
    entries.push((
        "F0.sol".into(),
        format!("{PRAGMA}import \"./F1.sol\";\ncontract F0 {{ }}\n"),
    ));
    for i in 1..20 {
        entries.push((
            format!("F{i}.sol"),
            format!(
                "{PRAGMA}import \"./F{}.sol\";\ninterface I{i} {{ }}\n",
                i + 1
            ),
        ));
    }
    entries.push((
        String::from("F20.sol"),
        format!("{PRAGMA}interface I20 {{ }}\n"),
    ));
    let files: BTreeMap<String, String> = entries.into_iter().collect();
    assert_eq!(reject_code(&files, "F0.sol"), "FE402");
}

#[test]
fn project_closure_over_64_files_is_fe402() {
    // A hub importing 70 leaves: the closure file-count cap fires (depth stays 1).
    let mut hub = String::from(PRAGMA);
    let mut entries: Vec<(String, String)> = Vec::new();
    for i in 0..70 {
        hub.push_str(&format!("import \"./L{i}.sol\";\n"));
        entries.push((
            format!("L{i}.sol"),
            format!("{PRAGMA}interface L{i} {{ }}\n"),
        ));
    }
    hub.push_str("contract Hub { }\n");
    entries.push(("Hub.sol".into(), hub));
    let files: BTreeMap<String, String> = entries.into_iter().collect();
    assert_eq!(reject_code(&files, "Hub.sol"), "FE402");
}

#[test]
fn project_entry_must_be_in_the_file_set() {
    let files = map(&[("A.sol", "pragma solidity ^0.8.20;\ncontract A { }\n")]);
    assert_eq!(reject_code(&files, "Missing.sol"), "FE476");
    // And an entry path with junk charset is gated by the same rule as imports.
    assert_eq!(reject_code(&files, "..\\A.sol"), "FE476");
}
