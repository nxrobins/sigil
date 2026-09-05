// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// SOL-AIRDROP (Rung C): the from-debit N-ary airdrop. The `_transfer`-in-loop over the
// parallel `recipients`/`amounts` arrays folds to the trusted atomic
// `self.balances.batch_transfer(__fe_sender, recipients, amounts)`; the length-equality
// `require` survives as a faithful `.len()` runtime check.
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
