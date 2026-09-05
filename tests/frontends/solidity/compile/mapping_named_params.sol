// SOL-SYNTAX: Solidity ≥0.8.18 NAMED mapping parameters — an optional documentation name after the
// key type and/or after the value type (`mapping(K name => V name)`). Pure syntax, zero semantic
// effect: the mapping lowers to the same bounded map as the unnamed form. Exercises key-named,
// value-named, both-named, and a NESTED mapping with a name on the outer value.
pragma solidity ^0.8.18;

contract Named {
    // Key-named.
    mapping(address owner => uint256) balances;
    // Value-named.
    mapping(address => uint256 amount) supply;
    // Both named.
    mapping(address holder => uint256 bal) ledger;
    // Nested — a name on the OUTER value (the inner mapping is the value type).
    mapping(address owner => mapping(address spender => uint256) allowed) allowances;

    function shift(address a, address b) public {
        uint256 x = balances[a];
        supply[b] = x;
        ledger[a] = x;
    }
}
