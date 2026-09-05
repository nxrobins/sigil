// SOL1b headline: a bounded token with the CANONICAL ERC20 `transfer` — caller
// authority via `msg.sender`, a `require` balance guard, and the debit/credit pair.
// The frontend recognizes the `bal[from] -= a; bal[to] += a;` idiom and folds it into
// ONE call to the TRUSTED `BoundedMap_u256_u256_64.transfer` (atomic checks-then-
// effects: balance + u256-overflow + bounded-ledger capacity all checked BEFORE any
// write, aliasing-correct for self-transfer). Overflow-safe + fund-safe by construction.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;

    function balanceOf(address who) public view returns (uint256) {
        return balances[who];
    }

    function transfer(address to, uint256 amount) public {
        require(balances[msg.sender] >= amount);
        balances[msg.sender] -= amount;
        balances[to] += amount;
    }
}
