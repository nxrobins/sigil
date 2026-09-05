// expect-fe: FE486
// SOL-CALLS: an internal function used in EXPRESSION position must be a single `return <expr>;`. `g`
// has a prior statement, so substituting its value would drop that statement (a dropped-effect risk).
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function g(uint256 v) internal returns (uint256) {
        uint256 t = v + 1;
        return t;
    }

    function f(uint256 v) public {
        x = g(v);
    }
}
