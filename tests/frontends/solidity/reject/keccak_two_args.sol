// expect-fe: FE401
// SOL-ACCESS EX-1: the fold's lookahead is EXACTLY `keccak256( <one string literal> )`.
// A two-argument call (not valid solc either) is NOT folded and fail-closes at the
// generic path - never a hash of partially-consumed arguments.
pragma solidity ^0.8.0;
contract C {
    bytes32 h;
    function f() public {
        h = keccak256("a", "b");
    }
}
