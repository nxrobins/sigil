// expect-fe: FE481
// A discarded `emit` must not silently drop a revert: `a - b` is checked arithmetic that traps on
// underflow in Solidity 0.8, so an emit argument containing it is rejected (bind it to a local first).
pragma solidity ^0.8.0;
contract C {
    function f(uint256 a, uint256 b) public {
        emit E(a - b);
    }
}
