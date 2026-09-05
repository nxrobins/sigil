//! SOL-AIRDROP M2 TDD smoke: a real from-debit airdrop must FOLD to `batch_transfer`
//! and the emitted SIGIL must compile through the trusted compiler. (Superseded by the
//! golden + reject fixtures in M3; kept minimal here to drive the recognizer.)

use sigil_compiler::compile_named_module;
use sigil_frontends::{Frontend, frontend_for};

fn sol() -> Box<dyn Frontend> {
    frontend_for("solidity").expect("solidity frontend registered")
}

const AIRDROP: &str = r#"// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Airdrop {
    mapping(address => uint256) balances;

    function _transfer(address from, address to, uint256 amount) internal {
        balances[from] -= amount;
        balances[to] += amount;
    }

    function airdrop(address[] calldata recipients, uint256[] calldata amounts) external {
        require(recipients.length == amounts.length);
        for (uint256 i = 0; i < recipients.length; i++) {
            _transfer(msg.sender, recipients[i], amounts[i]);
        }
    }
}
"#;

/// Golden generator (run manually, never in CI):
///   cargo test -p sigil-frontends --test airdrop_smoke gen_airdrop_goldens -- --ignored --nocapture
/// Translates every `compile/airdrop*.sol` with the SAME source_name the golden harness
/// uses (`p.to_str()`), writes the `.sigil`. Deterministic ⇒ `golden_translation` then matches.
#[test]
#[ignore]
fn gen_airdrop_goldens() {
    let dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/frontends/solidity/compile");
    let mut n = 0;
    for e in std::fs::read_dir(&dir).unwrap() {
        let p = e.unwrap().path();
        let stem = p.file_stem().and_then(|s| s.to_str()).unwrap_or("");
        if p.extension().and_then(|x| x.to_str()) != Some("sol") || !stem.starts_with("airdrop") {
            continue;
        }
        let src = std::fs::read_to_string(&p).unwrap();
        let emitted = sol()
            .translate(&src, p.to_str().unwrap())
            .unwrap_or_else(|d| panic!("gen: translate {p:?} failed: {d:?}"));
        let out = p.with_extension("sigil");
        std::fs::write(&out, &emitted.text).unwrap();
        eprintln!("wrote {out:?} ({} bytes)", emitted.text.len());
        n += 1;
    }
    assert!(n > 0, "no airdrop*.sol fixtures found in {dir:?}");
}

#[test]
fn airdrop_folds_to_batch_transfer_and_compiles() {
    let emitted = sol()
        .translate(AIRDROP, "airdrop.sol")
        .unwrap_or_else(|d| panic!("airdrop must translate, got {d:?}"));
    assert!(
        emitted.text.contains(".batch_transfer("),
        "the airdrop loop must fold to `batch_transfer`; emitted:\n{}",
        emitted.text
    );
    // The surviving `require(recipients.length == amounts.length)` must lower to `.len()`.
    assert!(
        emitted.text.contains(".len()"),
        "the length require must lower `.length` → `.len()`; emitted:\n{}",
        emitted.text
    );
    compile_named_module(emitted.source_name.clone(), emitted.text.clone()).unwrap_or_else(|e| {
        let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
        panic!(
            "emitted airdrop SIGIL must compile through the trusted compiler, got {codes:?}\n--- emitted ---\n{}",
            emitted.text
        )
    });
}
