// SOL-EVENTS: an `emit` statement with plain (read-only) args is DISCARDED, so `f`'s only statement
// vanishes and it translates to an empty-bodied method — the emit leaves no trace.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    function f(address to, uint256 amount) public { emit Transfer(msg.sender, to, amount); }
}
