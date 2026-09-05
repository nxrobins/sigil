// expect-fe: FE492
// Adversarial (defense-in-depth): a TWO-LEVEL launder of a per-leg-varying debit source
// through prelude aliases (`t = recipients[i]; f = t; balances[f] -= amounts[i];`). This is a
// multi-sender airdrop in disguise (each leg debits a DIFFERENT account) and must reject like
// `airdrop_multi_sender`. `fold_airdrop` resolves the `from` operand TRANSITIVELY through the
// let-prelude to `recipients[i]`, so the loop-invariance gate sees it is counter-varying →
// FE492 — the gate is self-sufficient, not reliant on the dropped-prelude → unresolved-ref path.
pragma solidity ^0.8.20;
contract C {
    mapping(address => uint256) balances;

    function airdrop(address[] calldata recipients, uint256[] calldata amounts) external {
        for (uint256 i = 0; i < recipients.length; i++) {
            address t = recipients[i];
            address f = t;
            balances[f] -= amounts[i];
            balances[recipients[i]] += amounts[i];
        }
    }
}
