// expect-fe: FE401
// SOL-ACCESS EX-1/AC-3: ONLY a string LITERAL argument folds. `keccak256(abi.encodePacked(...))`
// (the Permit/Governor typehash pattern) is a RUNTIME hash - folding it would bake a
// compile-time constant of the wrong bytes (MC-2). No runtime keccak intrinsic exists,
// so it stays blocked, never a garbage constant that compiles.
pragma solidity ^0.8.0;
contract C {
    bytes32 h;
    function f(uint256 a, uint256 b) public {
        h = keccak256(abi.encodePacked(a, b));
    }
}
