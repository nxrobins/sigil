//! SOL-AIRDROP end-to-end: translate a REAL from-debit airdrop contract through the
//! FRONTEND, wrap it with a `tool_main` that seeds balances + calls the translated
//! `airdrop` method with real `BoundedVec` inputs, and RUN it. This closes the loop the
//! goldens (fold) + `bt_*`/`prop_airdrop_matches_reference` (primitive semantics) leave
//! open: the emitted record wrapper + the surviving length `require` + the folded
//! `batch_transfer` call, composed, execute correctly on the actual translated artifact
//! — with aliasing (a duplicate recipient AND a `recipient == from` self-leg) exercised.
//! Mirrors `sol_uintn_spike.rs`'s translate-then-run harness (no `! { Alloc }`).

use sigil_compiler::compile_tool;
use sigil_frontends::frontend_for;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// The canonical from-debit airdrop. `require(recipients.length == amounts.length)` (the
/// UP-LENGTH survivor) + a `_transfer`-in-loop over the parallel arrays. Translated with
/// source name `tool.sol` ⇒ the emitted module is `module tool;` + `record Airdrop` +
/// `impl Airdrop { new(); airdrop() }` (the dead `_transfer` is swept, the loop folds).
const AIRDROP_SRC: &str = "pragma solidity ^0.8.20;\n\
contract Airdrop {\n\
    mapping(address => uint256) balances;\n\
    function _transfer(address from, address to, uint256 amount) internal {\n\
        balances[from] -= amount;\n\
        balances[to] += amount;\n\
    }\n\
    function airdrop(address[] calldata recipients, uint256[] calldata amounts) external {\n\
        require(recipients.length == amounts.length);\n\
        for (uint256 i = 0; i < recipients.length; i++) {\n\
            _transfer(msg.sender, recipients[i], amounts[i]);\n\
        }\n\
    }\n\
}\n";

/// Translate the airdrop contract and append a free `tool_main` running `body`. Asserts the
/// emitted artifact actually folded to `batch_transfer` (so the run exercises the real fold).
fn airdrop_tool(body: &str) -> String {
    let emitted = frontend_for("solidity")
        .unwrap()
        .translate(AIRDROP_SRC, "tool.sol")
        .expect("airdrop contract must translate")
        .text;
    assert!(
        emitted.contains(".batch_transfer(__fe_sender, recipients, amounts)"),
        "the airdrop must fold to batch_transfer:\n{emitted}"
    );
    format!("{emitted}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n")
}

/// A fresh seeded `Airdrop` with `balances[1] = 1000` (the sole holder / airdrop source).
const SEED_FROM_1000: &str = "    let mut m: BoundedMap_u256_u256_64 = BoundedMap_u256_u256_64::new();\n\
    let _s0: i64 = m.insert(1, 1000);\n\
    let mut a: Airdrop = Airdrop { balances: m };\n";

#[test]
fn translated_airdrop_runs_with_aliasing() {
    // from=1 (balance 1000); recipients [2, 2, 1], amounts [10, 20, 5]:
    //   leg0: 1→2  amt 10  ⇒ 1=990, 2=10
    //   leg1: 1→2  amt 20  ⇒ 1=970, 2=30   (DUPLICATE recipient — credits accumulate)
    //   leg2: 1→1  amt 5   ⇒ self-leg nets zero (still underflow-checked) ⇒ 1=970
    // Final: 1=970, 2=30. An alias-blind impl would get 2=20 (lost credit) or corrupt 1.
    let body = format!(
        "{SEED_FROM_1000}\
    let mut recips: BoundedVec_u256_64 = BoundedVec_u256_64::new();\n\
    let _r0: i64 = recips.push(2);\n\
    let _r1: i64 = recips.push(2);\n\
    let _r2: i64 = recips.push(1);\n\
    let mut amts: BoundedVec_u256_64 = BoundedVec_u256_64::new();\n\
    let _m0: i64 = amts.push(10);\n\
    let _m1: i64 = amts.push(20);\n\
    let _m2: i64 = amts.push(5);\n\
    a.airdrop(1, recips, amts);\n\
    let b1: u256 = a.balances.get_or(1, 0);\n\
    let b2: u256 = a.balances.get_or(2, 0);\n\
    if b1 == 970 {{ if b2 == 30 {{ return 0 - 88; }} else {{ return 0 - 999; }} }} else {{ return 0 - 998; }}"
    );
    let result =
        compile_tool(&airdrop_tool(&body)).expect("translated airdrop + tool_main must compile");
    match execute_ephemeral(
        &result.wasm,
        b"",
        result.fuel_budget.max(1_000_000_000),
        &IoGrants::none(),
    ) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message
                .find(p)
                .unwrap_or_else(|| panic!("no sentinel: {message}"))
                + p.len();
            let e = message[s..].find(')').unwrap();
            assert_eq!(
                &message[s..s + e],
                "88",
                "final balances must be 1=970, 2=30"
            );
        }
        other => panic!("expected the sentinel, got {other:?}"),
    }
}

#[test]
fn translated_airdrop_length_require_traps() {
    // The surviving `require(recipients.length == amounts.length)` (UP-LENGTH): 2 recipients,
    // 1 amount ⇒ `trap_if(!(2 == 1))` fires BEFORE the airdrop write — faithful to Solidity's
    // revert (and never silently airdropping with a truncated amounts array).
    let body = format!(
        "{SEED_FROM_1000}\
    let mut recips: BoundedVec_u256_64 = BoundedVec_u256_64::new();\n\
    let _r0: i64 = recips.push(2);\n\
    let _r1: i64 = recips.push(3);\n\
    let mut amts: BoundedVec_u256_64 = BoundedVec_u256_64::new();\n\
    let _m0: i64 = amts.push(10);\n\
    a.airdrop(1, recips, amts);\n\
    return 0 - 1;"
    );
    let result = compile_tool(&airdrop_tool(&body)).expect("compile");
    assert!(
        matches!(
            execute_ephemeral(
                &result.wasm,
                b"",
                result.fuel_budget.max(1_000_000_000),
                &IoGrants::none()
            ),
            Err(ToolError::Trapped { .. })
        ),
        "a length-mismatched airdrop must trap (the require survives as a runtime guard)"
    );
}
