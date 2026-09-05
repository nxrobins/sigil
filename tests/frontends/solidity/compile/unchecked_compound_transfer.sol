// SOL-UNCHECKED Part A alone: a compound `balances[from] -= amount` debit inside `unchecked`
// (the direct-slot form — no `fromBalance` local). `unwrap_unchecked` splices the block out; the
// existing `as_debit` compound arm folds debit+credit into the atomic `self.balances.transfer(...)`
// with no Part-B alias tracking needed. Proves the unwrap composes with the pre-existing fold.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;

    function move(address from, address to, uint256 amount) public {
        require(balances[from] >= amount);
        unchecked {
            balances[from] -= amount;
        }
        balances[to] += amount;
    }
}
