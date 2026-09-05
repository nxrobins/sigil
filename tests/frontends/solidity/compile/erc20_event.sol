// SOL-EVENTS: an `event` declaration is parse-and-DISCARDED (events carry no SIGIL state/funds/
// control effect), so this contract translates to a record with just the mapping field — the event
// leaves no trace in the output.
pragma solidity ^0.8.0;
contract C {
    event Transfer(address from, address to, uint256 amount);
    mapping(address => uint256) balances;
}
