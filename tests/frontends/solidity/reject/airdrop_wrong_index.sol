// expect-fe: FE492
// A loop shaped like an airdrop but the amount is read at the WRONG index (`amounts[i + 1]`, not
// the bare counter `amounts[i]`). The exact-shape gate requires every leg's amount to be
// `Index(amounts, Var(idx))` — a compound index fails it → FE492 (never a silent off-by-one fold).
pragma solidity ^0.8.20;
contract C {
    mapping(address => uint256) balances;

    function _transfer(address from, address to, uint256 amount) internal {
        balances[from] -= amount;
        balances[to] += amount;
    }

    function airdrop(address[] calldata recipients, uint256[] calldata amounts) external {
        for (uint256 i = 0; i < recipients.length; i++) {
            _transfer(msg.sender, recipients[i], amounts[i + 1]);
        }
    }
}
