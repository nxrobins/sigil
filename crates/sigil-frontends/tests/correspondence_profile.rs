//! Drift-pinned correspondence profile for the shipped foreign frontends.
//!
//! The frontend implementations are untrusted translators. This test binds their
//! documented source subsets to concrete evidence: exact fixture counts, exact
//! reject-code coverage, compiler acceptance of emitted goldens, and an
//! independently written scalar-expression oracle for every shipped frontend.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use sigil_compiler::compile_named_module;
use sigil_frontends::frontend_for;

const PROFILE: &str = include_str!("../../../docs/specs/foreign-frontend-correspondence.md");
const FOREIGN_SPEC: &str = include_str!("../../../docs/specs/foreign-frontends.md");
const RESIDUAL_RISKS: &str = include_str!("../../../docs/RESIDUAL_RISKS.md");
const SOUNDNESS_MATRIX: &str = include_str!("../../../docs/SOUNDNESS_MATRIX.md");
const FRONTEND_REGISTRY: &str = include_str!("../src/lib.rs");

#[derive(Clone, Copy)]
struct FrontendProfile {
    language: &'static str,
    alias: &'static str,
    extension: &'static str,
    compile_pin: usize,
    reject_pin: usize,
    reject_code_pin: usize,
}

const PROFILES: &[FrontendProfile] = &[
    FrontendProfile {
        language: "typescript",
        alias: "ts",
        extension: "ts",
        compile_pin: 7,
        reject_pin: 22,
        reject_code_pin: 17,
    },
    FrontendProfile {
        language: "rust",
        alias: "rs",
        extension: "rs",
        compile_pin: 26,
        reject_pin: 56,
        reject_code_pin: 26,
    },
    FrontendProfile {
        language: "solidity",
        alias: "sol",
        extension: "sol",
        compile_pin: 71,
        reject_pin: 184,
        reject_code_pin: 55,
    },
];

const SCALAR_ORACLE_CASES_PER_FRONTEND: usize = 80;

#[derive(Clone)]
struct ScalarExpr {
    source: String,
    sigil: String,
}

#[test]
fn correspondence_profiles_are_drift_pinned() {
    assert!(PROFILE.contains("Profile:** `FFC-2026-09-07`"));
    assert!(
        PROFILE
            .contains("Machine gate:** `crates/sigil-frontends/tests/correspondence_profile.rs`")
    );
    assert!(PROFILE.contains("PIN_FRONTEND_PROFILE_COUNT = 3"));
    assert!(PROFILE.contains("PIN_SCALAR_ORACLE_CASES_PER_FRONTEND = 80"));
    assert!(
        normalized_whitespace(FOREIGN_SPEC)
            .contains("The translator is never trusted; **SIGIL is the trust anchor**")
    );
    assert!(RESIDUAL_RISKS.contains("| SR-012 | Medium | Closed |"));
    assert!(SOUNDNESS_MATRIX.contains("FFC-2026-09-07"));

    for token in [
        "unsupported syntax",
        "name/scope capture",
        "numeric/layout boundaries",
        "control flow",
        "effects",
        "diagnostic preservation",
        "Every allow-list expansion requires explicit review and renewed evidence",
    ] {
        assert!(
            PROFILE.contains(token),
            "correspondence profile lost required review/evidence token: {token}"
        );
    }

    for profile in PROFILES {
        let frontend = frontend_for(profile.language)
            .unwrap_or_else(|| panic!("frontend `{}` must be registered", profile.language));
        assert_eq!(frontend.name(), profile.language);
        let alias = frontend_for(profile.alias)
            .unwrap_or_else(|| panic!("frontend alias `{}` must be registered", profile.alias));
        assert_eq!(alias.name(), profile.language);

        assert!(
            PROFILE.contains(&format!(
                "PIN_{}_COMPILE_FIXTURES = {}",
                profile.language.to_uppercase(),
                profile.compile_pin
            )),
            "profile doc lost compile pin for {}",
            profile.language
        );
        assert!(
            PROFILE.contains(&format!(
                "PIN_{}_REJECT_FIXTURES = {}",
                profile.language.to_uppercase(),
                profile.reject_pin
            )),
            "profile doc lost reject pin for {}",
            profile.language
        );
        assert!(
            PROFILE.contains(&format!(
                "PIN_{}_REJECT_CODES = {}",
                profile.language.to_uppercase(),
                profile.reject_code_pin
            )),
            "profile doc lost reject-code pin for {}",
            profile.language
        );

        let compile = frontend_files(profile.language, "compile", profile.extension);
        let reject = frontend_files(profile.language, "reject", profile.extension);
        assert_eq!(
            compile.len(),
            profile.compile_pin,
            "{} accepted fixture surface changed; update FFC-2026-09-07",
            profile.language
        );
        assert_eq!(
            reject.len(),
            profile.reject_pin,
            "{} rejected fixture surface changed; update FFC-2026-09-07",
            profile.language
        );

        let mut reject_codes = BTreeSet::new();
        for fixture in &reject {
            let source = std::fs::read_to_string(fixture)
                .unwrap_or_else(|err| panic!("cannot read {}: {err}", fixture.display()));
            let code = expected_fe_code(&source)
                .unwrap_or_else(|| panic!("{} has no // expect-fe: header", fixture.display()));
            reject_codes.insert(code.to_owned());
        }
        assert_eq!(
            reject_codes.len(),
            profile.reject_code_pin,
            "{} reject-code surface changed; update FFC-2026-09-07",
            profile.language
        );

        for fixture in &compile {
            assert!(
                fixture.with_extension("sigil").is_file(),
                "accepted fixture {} needs an independent SIGIL golden",
                fixture.display()
            );
        }
    }

    for exact_arm in [
        "\"typescript\" | \"ts\" => Some(Box::new(typescript::TypeScriptFrontend))",
        "\"solidity\" | \"sol\" => Some(Box::new(solidity::SolidityFrontend))",
        "\"rust\" | \"rs\" => Some(Box::new(rust::RustFrontend))",
    ] {
        assert!(
            FRONTEND_REGISTRY.contains(exact_arm),
            "frontend registry drifted without updating the correspondence profile: {exact_arm}"
        );
    }
}

#[test]
fn accepted_fixtures_match_goldens_and_compile() {
    for profile in PROFILES {
        let frontend = frontend_for(profile.language)
            .unwrap_or_else(|| panic!("frontend `{}` must be registered", profile.language));
        for fixture in frontend_files(profile.language, "compile", profile.extension) {
            let source = std::fs::read_to_string(&fixture)
                .unwrap_or_else(|err| panic!("cannot read {}: {err}", fixture.display()));
            let expected =
                std::fs::read_to_string(fixture.with_extension("sigil")).unwrap_or_else(|err| {
                    panic!("cannot read golden for {}: {err}", fixture.display())
                });
            let emitted = frontend
                .translate(&source, fixture.to_str().expect("fixture path is UTF-8"))
                .unwrap_or_else(|diags| {
                    panic!("{} rejected accepted fixture: {diags:?}", fixture.display())
                });
            assert_eq!(
                normalize(&emitted.text),
                normalize(&expected),
                "golden drift for {}",
                fixture.display()
            );
            compile_named_module(emitted.source_name.clone(), emitted.text.clone()).unwrap_or_else(
                |err| {
                    panic!(
                        "emitted SIGIL for {} failed trusted compilation: {:?}",
                        fixture.display(),
                        err.diagnostics()
                    )
                },
            );
        }
    }
}

#[test]
fn scalar_expression_core_matches_independent_oracle() {
    let cases = scalar_oracle_cases();
    assert_eq!(cases.len(), SCALAR_ORACLE_CASES_PER_FRONTEND);

    for (index, case) in cases.iter().enumerate() {
        assert_oracle_case(
            "typescript",
            &typescript_source(&case.source),
            &format!("oracle_ts_{index}.ts"),
            &expected_ts_or_rs(&format!("oracle_ts_{index}"), "i64", &case.sigil),
        );
        assert_oracle_case(
            "rust",
            &rust_source(&case.source),
            &format!("oracle_rs_{index}.rs"),
            &expected_ts_or_rs(&format!("oracle_rs_{index}"), "i64", &case.sigil),
        );
        assert_oracle_case(
            "solidity",
            &solidity_source(&case.source),
            &format!("oracle_sol_{index}.sol"),
            &expected_solidity(&format!("oracle_sol_{index}"), &case.sigil),
        );
    }
}

fn assert_oracle_case(language: &str, source: &str, source_name: &str, expected: &str) {
    let frontend =
        frontend_for(language).unwrap_or_else(|| panic!("frontend `{language}` must exist"));
    let emitted = frontend
        .translate(source, source_name)
        .unwrap_or_else(|diags| panic!("{language} oracle case rejected: {diags:?}\n{source}"));
    assert_eq!(
        normalize(&emitted.text),
        normalize(expected),
        "{language} oracle emission drift for {source_name}\nsource:\n{source}"
    );
    compile_named_module(emitted.source_name, emitted.text).unwrap_or_else(|err| {
        panic!(
            "{language} oracle output failed trusted compilation: {:?}",
            err.diagnostics()
        )
    });
}

fn scalar_oracle_cases() -> Vec<ScalarExpr> {
    let atoms = ["a", "b", "0", "1", "2"];
    let mut cases = atoms
        .iter()
        .map(|atom| ScalarExpr {
            source: (*atom).to_owned(),
            sigil: (*atom).to_owned(),
        })
        .collect::<Vec<_>>();
    for op in ["+", "-", "*"] {
        for left in atoms {
            for right in atoms {
                let expr = format!("({left} {op} {right})");
                cases.push(ScalarExpr {
                    source: expr.clone(),
                    sigil: expr,
                });
            }
        }
    }
    cases
}

fn typescript_source(expr: &str) -> String {
    format!("function f(a: number, b: number): number {{\n  return {expr};\n}}\n")
}

fn rust_source(expr: &str) -> String {
    format!("pub fn f(a: i64, b: i64) -> i64 {{ {expr} }}\n")
}

fn solidity_source(expr: &str) -> String {
    format!(
        "pragma solidity ^0.8.0;\ncontract C {{\n    function f(uint256 a, uint256 b) public pure returns (uint256) {{\n        return {expr};\n    }}\n}}\n"
    )
}

fn expected_ts_or_rs(module: &str, ty: &str, expr: &str) -> String {
    format!("module {module};\npub fn f(a: {ty}, b: {ty}) -> {ty} {{\n  return {expr};\n}}\n")
}

fn expected_solidity(module: &str, expr: &str) -> String {
    format!(
        "module {module};\n\nrecord C {{ __fe_unit: bool }}\n\nimpl C {{\n    pub fn new() -> C {{\n        return C {{ __fe_unit: false }};\n    }}\n\n    pub fn f(self: C, a: u256, b: u256) -> u256 {{\n        return {expr};\n    }}\n}}\n"
    )
}

fn frontend_files(language: &str, subdir: &str, extension: &str) -> Vec<PathBuf> {
    let dir = frontend_root().join(language).join(subdir);
    let mut files = std::fs::read_dir(&dir)
        .unwrap_or_else(|err| panic!("cannot read {}: {err}", dir.display()))
        .map(|entry| entry.expect("directory entry is readable").path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some(extension))
        .collect::<Vec<_>>();
    files.sort();
    files
}

fn frontend_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/frontends")
}

fn expected_fe_code(source: &str) -> Option<&str> {
    source
        .lines()
        .find_map(|line| line.trim().strip_prefix("// expect-fe:"))
        .map(str::trim)
}

fn normalize(source: &str) -> String {
    source.replace("\r\n", "\n")
}

fn normalized_whitespace(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}
