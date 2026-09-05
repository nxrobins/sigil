// expect-fe: FE401
// An explicit width cast `uint8(a)` is a call to a non-struct name → unsupported (the
// truncating-cast semantics + the SafeCast idiom are a deferred follow-on; anti-goal).
pragma solidity ^0.8.0;
contract C {
    function f(uint256 a) public pure returns (uint8) {
        return uint8(a);
    }
}
