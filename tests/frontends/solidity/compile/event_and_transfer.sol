// SOL-EVENTS: an `emit` sitting BETWEEN the balance debit and credit is discarded, which makes the
// two writes adjacent — so the transfer recognizer still folds them into the atomic `.transfer(...)`
// (discarding an interleaved emit HELPS the fold). The event declaration is dropped too.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    event Transfer(address indexed from, address indexed to, uint256 value);
    function transfer(address to, uint256 amount) public {
        balances[msg.sender] -= amount;
        emit Transfer(msg.sender, to, amount);
        balances[to] += amount;
    }
}
