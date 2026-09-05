//! Wasm-size paired-program driver.
//!
//! Walks `bench/wasm-size/0N_<slug>/` and enforces seven structural
//! contracts plus two cross-link contracts. Every adversarial review fence
//! MC-1, MC-2, MI-5, MI-11, UP-14, plus the structural v2 fences, is closed
//! here.
//!
//! NOT enforced by this driver:
//!   - Behavioural equivalence between SIGIL and Rust modules in
//!     wasmtime. Four of five SIGIL fixtures require host-import
//!     stubs (spawn/send/alloc/FFI/fuel) that would add a mini-
//!     runtime to the driver. Equivalence is verified by manual
//!     inspection of each SPEC.md instead, and PERFORMANCE.md
//!     discloses this honestly.
//!   - Measured byte counts (those are reproducibility-driven,
//!     captured by `examples/wasm_size`, not invariant).

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use sigil_compiler::compile_named_module;

const EXPECTED_PAIRS: usize = 5;

const REQUIRED_FILES: &[&str] = &["SPEC.md", "main.sigil", "main.rs", "Cargo.toml"];

const PROFILE_RELEASE_BLOCK: &str = r#"[profile.release]
opt-level = "s"
panic = "abort"
lto = true
strip = true
codegen-units = 1"#;

const SPEC_FIELDS: &[&str] = &["Input:", "Expected output:", "Error mode:", "Exit code:"];

/// Per-slug regexes (substring or NOT substring) verifying that the
/// SIGIL fixture actually invokes the feature its slug advertises.
/// Closes MC-1: a lazy implementer cannot ship a no-op fixture and
/// claim the slug-named feature.
fn feature_invocation(slug: &str) -> Vec<(bool, &'static str)> {
    // (must_contain, needle). must_contain=false means "must NOT contain".
    match slug {
        "fib" => vec![(true, "fn fib"), (false, "! {")],
        "echo_actor" => vec![(true, "spawn::<"), (true, "actor")],
        "json_sum" => vec![(true, "! { Alloc"), (true, "alloc(")],
        "bounded_loop" => vec![(true, "while ")],
        "file_read_cap" => vec![(true, "! { FFI"), (true, "extern \"C\"")],
        _ => vec![],
    }
}

fn workspace_root() -> PathBuf {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest_dir
        .parent()
        .and_then(|p| p.parent())
        .map(|p| p.to_path_buf())
        .expect("workspace root")
}

fn pairs_dir() -> PathBuf {
    workspace_root().join("bench").join("wasm-size")
}

#[derive(Debug, Clone)]
struct PairEntry {
    number: u32,
    slug: String,
    dir: PathBuf,
}

fn parse_dir_name(name: &str) -> Option<(u32, String)> {
    let bytes = name.as_bytes();
    if bytes.len() < 4 {
        return None;
    }
    if !bytes[0].is_ascii_digit() || !bytes[1].is_ascii_digit() || bytes[2] != b'_' {
        return None;
    }
    let num: u32 = name[..2].parse().ok()?;
    let slug = name[3..].to_string();
    Some((num, slug))
}

fn load_pairs() -> Vec<PairEntry> {
    let dir = pairs_dir();
    let mut out = Vec::new();
    let entries = match fs::read_dir(&dir) {
        Ok(e) => e,
        Err(_) => return out,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if !path.is_dir() {
            continue;
        }
        let name = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
        if let Some((number, slug)) = parse_dir_name(name) {
            out.push(PairEntry {
                number,
                slug,
                dir: path,
            });
        }
    }
    out.sort_by_key(|p| p.number);
    out
}

#[test]
fn pair_count_is_expected() {
    let pairs = load_pairs();
    assert_eq!(
        pairs.len(),
        EXPECTED_PAIRS,
        "expected {EXPECTED_PAIRS} pairs in bench/wasm-size/, got {}",
        pairs.len()
    );
}

/// Check 1: pair structure — each 0N_<slug>/ has exactly the
/// required files; no missing.
#[test]
fn pair_structure_complete() {
    let pairs = load_pairs();
    assert!(!pairs.is_empty(), "no pairs found");
    for pair in &pairs {
        for required in REQUIRED_FILES {
            let path = pair.dir.join(required);
            assert!(
                path.is_file(),
                "pair 0{}: missing {}",
                pair.number,
                path.display()
            );
        }
    }
}

/// Check 2: SIGIL fixtures compile cleanly (zero diagnostics).
#[test]
fn sigil_fixtures_compile_clean() {
    let pairs = load_pairs();
    for pair in &pairs {
        let src = pair.dir.join("main.sigil");
        let source = fs::read_to_string(&src).expect("read main.sigil");
        let result = compile_named_module(format!("0{}_{}", pair.number, pair.slug), source);
        match result {
            Ok(_) => {}
            Err(e) => {
                let diags: Vec<String> = e
                    .diagnostics()
                    .iter()
                    .map(|d| format!("{:?}: {}", d.code(), d.message()))
                    .collect();
                panic!(
                    "pair 0{}_{}: SIGIL fixture must compile cleanly. Diagnostics:\n{}",
                    pair.number,
                    pair.slug,
                    diags.join("\n")
                );
            }
        }
    }
}

/// Check 3: SIGIL fixture invokes the feature its slug advertises
/// (MC-1: closes the no-op fixture loophole).
#[test]
fn sigil_invokes_named_feature() {
    let pairs = load_pairs();
    for pair in &pairs {
        let src = pair.dir.join("main.sigil");
        let source = fs::read_to_string(&src).expect("read main.sigil");
        for (must_contain, needle) in feature_invocation(&pair.slug) {
            let present = source.contains(needle);
            if must_contain {
                assert!(
                    present,
                    "pair 0{}_{}: main.sigil must invoke `{}` (feature anchor for slug)",
                    pair.number, pair.slug, needle
                );
            } else {
                assert!(
                    !present,
                    "pair 0{}_{}: main.sigil must NOT contain `{}` (feature anchor for slug)",
                    pair.number, pair.slug, needle
                );
            }
        }
    }
}

/// Check 4: Rust Cargo.toml pins the mandated [profile.release]
/// block verbatim (MC-2: closes the asymmetric-Rust-overhead attack).
#[test]
fn rust_release_profile_pinned() {
    let pairs = load_pairs();
    for pair in &pairs {
        let manifest = pair.dir.join("Cargo.toml");
        let text = fs::read_to_string(&manifest).expect("read Cargo.toml");
        assert!(
            text.contains(PROFILE_RELEASE_BLOCK),
            "pair 0{}_{}: Cargo.toml must contain the mandated `[profile.release]` block verbatim. \
             The block pins opt-level=\"s\", panic=\"abort\", lto=true, strip=true, codegen-units=1. \
             Got Cargo.toml:\n{}",
            pair.number,
            pair.slug,
            text
        );
        assert!(
            text.contains(r#"crate-type = ["cdylib"]"#),
            "pair 0{}_{}: Cargo.toml must declare `crate-type = [\"cdylib\"]`",
            pair.number,
            pair.slug
        );
    }
}

/// Check 4b: every compiled SIGIL module is VALID WebAssembly.
/// Added after wasm-opt exposed an i64-base-pointer load in the
/// echo_actor inner module: these fixtures are byte-measured but
/// never instantiated, so nothing else validates them.
#[test]
fn sigil_modules_validate_as_wasm() {
    let pairs = load_pairs();
    for pair in &pairs {
        let src = pair.dir.join("main.sigil");
        let source = fs::read_to_string(&src).expect("read main.sigil");
        let comp = compile_named_module(format!("0{}_{}", pair.number, pair.slug), source)
            .expect("SIGIL fixture compiles cleanly");
        let mut modules = vec![("inner", comp.wasm_inner.clone())];
        if let Some(outer) = &comp.wasm_outer {
            modules.push(("outer", outer.clone()));
        }
        for (label, bytes) in modules {
            wasmparser::Validator::new()
                .validate_all(&bytes)
                .unwrap_or_else(|e| {
                    panic!(
                        "pair 0{}_{}: {} module is not valid Wasm: {e}",
                        pair.number, pair.slug, label
                    )
                });
        }
    }
}

/// Check 5: SPEC.md schema — four named fields present (MI-11: closes
/// the loose-contract loophole).
#[test]
fn spec_schema_complete() {
    let pairs = load_pairs();
    for pair in &pairs {
        let spec = pair.dir.join("SPEC.md");
        let text = fs::read_to_string(&spec).expect("read SPEC.md");
        for field in SPEC_FIELDS {
            assert!(
                text.contains(field),
                "pair 0{}_{}: SPEC.md must contain field `{}` — found:\n{}",
                pair.number,
                pair.slug,
                field,
                text
            );
        }
    }
}

/// Check 6: numbering is contiguous 01..05 and every slug appears in
/// PERFORMANCE.md (UP-14: closes the gap-in-numbering loophole +
/// pins the published table against drift).
#[test]
fn numbering_contiguous_and_slugs_in_performance_md() {
    let pairs = load_pairs();
    let numbers: BTreeSet<u32> = pairs.iter().map(|p| p.number).collect();
    let expected: BTreeSet<u32> = (1..=EXPECTED_PAIRS as u32).collect();
    assert_eq!(
        numbers, expected,
        "pair numbers must be contiguous 01..{:02} with no gaps or duplicates",
        EXPECTED_PAIRS
    );

    let perf_path = workspace_root().join("PERFORMANCE.md");
    if !perf_path.is_file() {
        return; // PERFORMANCE.md is written after the driver; check is a
        // no-op until the doc lands. The cross_links_intact test
        // enforces the file exists.
    }
    let perf = fs::read_to_string(&perf_path).expect("read PERFORMANCE.md");
    for pair in &pairs {
        let dir_name = format!("0{}_{}", pair.number, pair.slug);
        assert!(
            perf.contains(&dir_name),
            "PERFORMANCE.md must mention slug `{}` (driver-pinned to bench/wasm-size/ dirs). \
             Found neither the row nor any reference.",
            dir_name
        );
    }
}

/// Check 7: rust-toolchain.toml exists and parses (MI-5: pins rustc
/// version for reproducibility).
#[test]
fn rust_toolchain_pinned() {
    let path = pairs_dir().join("rust-toolchain.toml");
    assert!(
        path.is_file(),
        "bench/wasm-size/rust-toolchain.toml is required (pins rustc version)"
    );
    let text = fs::read_to_string(&path).expect("read rust-toolchain.toml");
    assert!(
        text.contains("[toolchain]"),
        "rust-toolchain.toml must have a `[toolchain]` table"
    );
    assert!(
        text.contains("wasm32-unknown-unknown"),
        "rust-toolchain.toml must list wasm32-unknown-unknown in `targets`"
    );
}

/// Check 8: cross-links between PERFORMANCE.md, COMPARISON.md, and
/// README.md.
#[test]
fn cross_links_intact() {
    let root = workspace_root();
    let perf_path = root.join("PERFORMANCE.md");
    let comp_path = root.join("COMPARISON.md");
    let readme_path = root.join("README.md");

    assert!(
        perf_path.is_file(),
        "PERFORMANCE.md must exist at repo root"
    );
    assert!(comp_path.is_file(), "COMPARISON.md must exist at repo root");
    assert!(readme_path.is_file(), "README.md must exist at repo root");

    let perf = fs::read_to_string(&perf_path).expect("read PERFORMANCE.md");
    let comp = fs::read_to_string(&comp_path).expect("read COMPARISON.md");
    let readme = fs::read_to_string(&readme_path).expect("read README.md");

    assert!(
        perf.contains("COMPARISON.md"),
        "PERFORMANCE.md must link to COMPARISON.md"
    );
    assert!(
        comp.contains("PERFORMANCE.md"),
        "COMPARISON.md must link to PERFORMANCE.md"
    );
    assert!(
        readme.contains("PERFORMANCE.md"),
        "README.md must link to PERFORMANCE.md"
    );
    assert!(
        readme.contains("COMPARISON.md"),
        "README.md must link to COMPARISON.md"
    );
}

/// Check 9: citation pre-flight exists and is referenced from
/// COMPARISON.md. Closes UP-6 (citation pre-flight has actually been
/// done before COMPARISON.md was written).
#[test]
fn comparison_uses_preflight() {
    let preflight = workspace_root()
        .join("bench")
        .join("comparison")
        .join("PRE-FLIGHT.md");
    assert!(
        preflight.is_file(),
        "bench/comparison/PRE-FLIGHT.md must exist (citation pre-flight is the source of truth)"
    );
    let comp_path = workspace_root().join("COMPARISON.md");
    if !comp_path.is_file() {
        return;
    }
    let comp = fs::read_to_string(&comp_path).expect("read COMPARISON.md");
    assert!(
        comp.contains("PRE-FLIGHT.md") || comp.contains("bench/comparison"),
        "COMPARISON.md must reference bench/comparison/PRE-FLIGHT.md (its citation source)"
    );
}
