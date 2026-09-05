//! SC-7 differential oracle (DEV-ONLY): the shipped RS0 parser is hand-rolled, but
//! a `syn` cross-check asserts every in-subset compile fixture is real,
//! `rustc`-parseable Rust — the "accept-set ⊆ real Rust" direction. `syn` is never
//! on the shipped/liveness path (it is a `[dev-dependencies]` entry), so it costs
//! zero trust and its own recursion never sees adversarial input (only the bounded
//! fixture corpus). Full normalized-AST structural comparison is the SC-7 target
//! for a later increment; this establishes the oracle.

use std::path::PathBuf;

fn compile_fixtures() -> Vec<PathBuf> {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/frontends/rust/compile");
    let mut v: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("read {dir:?}: {e}"))
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().and_then(|x| x.to_str()) == Some("rs"))
        .collect();
    v.sort();
    v
}

/// Every RS0 compile fixture must parse as real Rust — if our hand-rolled parser
/// accepts something `syn` rejects, the fixture is not actually Rust and the
/// "translate a Rust subset" claim is violated.
#[test]
fn compile_fixtures_are_real_rust() {
    let files = compile_fixtures();
    assert!(!files.is_empty(), "expected RS0 compile fixtures");
    for p in files {
        let src = std::fs::read_to_string(&p).unwrap();
        syn::parse_file(&src)
            .unwrap_or_else(|e| panic!("compile fixture {p:?} is not valid Rust (syn): {e}"));
    }
}
