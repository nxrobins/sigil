// expect-fe: FE462
// EX-2: `uintN op uint256` is mixed-width arithmetic → rejected (which width's trap?). The
// narrow operand must be widened with an explicit cast.
pragma solidity ^0.8.0;
contract C {
    function f(uint128 a, uint256 b) public pure returns (uint256) {
        return a + b;
    }
}
