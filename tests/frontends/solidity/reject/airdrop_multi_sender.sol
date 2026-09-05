// expect-fe: FE492
// The debit source varies per leg (`senders[i]`, not a loop-invariant `from`). The exact-shape
// gate requires `from` to be loop-invariant + pure; an `Index`-on-counter source fails it → FE492.
// A per-leg-varying sender is a fundamentally different (unfoldable) operation, not an airdrop.
pragma solidity ^0.8.20;
contract C {
    mapping(address => uint256) balances;

    function _transfer(address from, address to, uint256 amount) internal {
        balances[from] -= amount;
        balances[to] += amount;
    }

    function airdrop(
        address[] calldata senders,
        address[] calldata recipients,
        uint256[] calldata amounts
    ) external {
        for (uint256 i = 0; i < recipients.length; i++) {
            _transfer(senders[i], recipients[i], amounts[i]);
        }
    }
}
