// expect-fe: FE448
// SOL-ACCESS: a modifier is now applied WITH its declared arguments, so the arity must
// match — a parameterless `onlyOwner()` applied with an argument (`onlyOwner(5)`) is an
// arity mismatch (0 params, 1 arg), rejected fail-closed rather than silently binding.
pragma solidity ^0.8.0;
contract C {
    uint256 x;
    modifier onlyOwner() { _; }
    function setX(uint256 v) public onlyOwner(5) { x = v; }
}
