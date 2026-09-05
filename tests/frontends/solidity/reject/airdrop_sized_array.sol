// expect-fe: FE491
// Only a single unsized `[]` on a scalar element is accepted (→ `BoundedVec_u256_64`). A SIZED
// array `[3]` (and `[][]` 2-D, array-of-mapping) is rejected at parse → FE491. The bound is the
// fixed BoundedVec capacity, not a user-chosen size the emitter can't honor.
pragma solidity ^0.8.20;
contract C {
    function f(uint256[3] calldata xs) external {}
}
