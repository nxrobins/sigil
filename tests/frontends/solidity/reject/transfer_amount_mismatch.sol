// expect-fe: FE412
// Only a MATCHING debit/credit pair folds into the atomic transfer; mismatched
// amounts are two independent map writes, so the second (trap-capable insert after a
// committed write) is FE412 — fail-closed, never an unsafe partial-state translation.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) bal;
    function f(address a, address b, uint256 x, uint256 y) public {
        bal[a] -= x;
        bal[b] += y;
    }
}
