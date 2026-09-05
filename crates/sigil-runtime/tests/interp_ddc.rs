//! THE DDC COMPARISON (docs/CLAIMS.md claim 40, HB-3) — its own gated test target.
//!
//! `interpret(S)` applied to `S` must reproduce `seed/sigil-seed.wasm` byte-for-byte, where the
//! interpreter is `interp/`: Python, no Rust, no build step, no third-party packages, nothing
//! ported from `crates/sigil-compiler/`. If the seed's BINARY ever contained logic absent from its
//! SOURCE, this is the check that notices, because an interpreter only ever does what the source
//! says.
//!
//! WHY IT IS FEATURE-GATED. Measured: the comparison takes ~8 min under CPython locally and
//! ~2 min under PyPy in CI (the input-mutation witness adds a second compile on top). Running it
//! inside `cargo test --workspace` pushed the `test` lane past its 30-minute timeout. CI lanes
//! carry no `needs:` between them, so they run in parallel and the wall-clock cost of a PR is the
//! SLOWEST lane, not the sum: moving this into a lane of its own returns `test` to ~22 minutes
//! and makes the comparison effectively free, which beats any interpreter speed-up.
//!
//! WHY THAT IS NOT A LOOPHOLE. A feature gate is a second way to own a proof that never runs —
//! precisely the hole `pin6_no_claim_is_proven_by_an_ignored_test` closes for `#[ignore]`, and one
//! the ledger's name-based checks cannot see. `interp_ddc_lane_is_wired_in_ci` (in
//! `interp_corpus.rs`, which DOES run by default) reads the workflow and asserts a lane actually
//! invokes this target. Gating a claim's proof without an equivalent check is not allowed.
//!
//!     cargo test -p sigil-runtime --test interp_ddc --no-default-features --features ddc

/// Run a script under `interp/` and return its stdout, failing loudly on a non-zero exit.
///
/// Python is already a hard dependency of this repository (the hygiene lane lints `bench/` and
/// `interp/` with ruff), so a missing interpreter is a broken environment and must FAIL rather
/// than silently skip — a skipped proof is the failure mode the ledger exists to prevent.
///
/// (Duplicated from `interp_corpus.rs`: each integration test is its own crate, so there is no
/// import to share. Keeping the two in step is cheap; sharing them via a `#[path]` module would
/// drag that file's whole wasmtime-backed corpus into this target for one helper.)
fn run_interp_script(name: &str, context: &str) -> String {
    let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("sigil-runtime lives under crates/");
    let script = repo.join("interp").join(name);

    let mut last_err = String::new();
    for exe in ["python3", "python"] {
        match std::process::Command::new(exe).arg(&script).output() {
            Ok(out) => {
                let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
                let stderr = String::from_utf8_lossy(&out.stderr);
                assert!(
                    out.status.success(),
                    "{context}\n--- stdout ---\n{stdout}\n--- stderr ---\n{stderr}"
                );
                return stdout;
            }
            Err(e) => last_err = format!("{exe}: {e}"),
        }
    }
    panic!(
        "no Python interpreter found ({last_err}). Python is required by this repository \
         (the hygiene lane lints bench/ and interp/); this proof cannot be skipped."
    );
}

#[test]
fn interp_ddc_reproduces_the_committed_seed() {
    let stdout = run_interp_script(
        "ddc.py",
        "the independent interpreter did NOT reproduce the committed seed. If the certified \
         source changed, the seed must be regenerated in the same change. If it did not, this is \
         a trusting-trust alarm: the seed's binary and its source disagree, or the two \
         implementations disagree about the language.",
    );
    assert!(
        stdout.contains("DDC HOLDS"),
        "ddc.py exited 0 without reporting the verdict — it may not have run the comparison at \
         all:\n{stdout}"
    );
    // The anti-vacuity witness must be the INPUT-MUTATION probe, not the earlier phrasing. Two
    // previous witnesses were vacuous with respect to the verdict — both were defeated by a stub
    // that ignores its input and replays the seed's bytes — and this assertion tracked one of
    // them, a line printed unconditionally on success. Assert on the probe that can actually fail.
    assert!(
        stdout.contains("the output depends on the input"),
        "ddc.py did not report the input-mutation probe, so the verdict is unwitnessed. A verdict \
         without it cannot distinguish a computing interpreter from one replaying stored \
         bytes:\n{stdout}"
    );
}
