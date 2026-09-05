// expect-fe: FE462
// EX-2: mixed-width arithmetic (`uint128 + uint64`) is rejected — a single node has no one
// unambiguous 2^N bound. Solidity widens implicitly; here it needs an explicit cast.
// (Over-rejection, fail-closed — a declared anti-goal.)
pragma solidity ^0.8.0;
contract C {
    function f(uint128 a, uint64 b) public pure returns (uint128) {
        return a + b;
    }
}
