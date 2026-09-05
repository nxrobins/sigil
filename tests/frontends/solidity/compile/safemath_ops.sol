// SOL-SAFEMATH: each of the five unsigned SafeMath ops folds to its CHECKED SIGIL operator
// (`.add`→`+`, `.sub`→`-`, `.mul`→`*`, `.div`→`/`, `.mod`→`%`; `/` and `%` trap on divide-by-zero
// exactly as SafeMath reverts). The `.sub(y,"msg")` message form drops the revert-message string. A
// chained `a.add(b).sub(c)` folds left-to-right into nested checked binops. (Pure functions so each is
// an isolated computation with no CEI interaction.)
pragma solidity ^0.8.0;
contract C {
    using SafeMath for uint256;

    function fadd(uint256 a, uint256 b) public pure returns (uint256) { return a.add(b); }
    function fsub(uint256 a, uint256 b) public pure returns (uint256) { return a.sub(b, "underflow"); }
    function fmul(uint256 a, uint256 b) public pure returns (uint256) { return a.mul(b); }
    function fdiv(uint256 a, uint256 b) public pure returns (uint256) { return a.div(b); }
    function fmod(uint256 a, uint256 b) public pure returns (uint256) { return a.mod(b); }
    function chain(uint256 a, uint256 b, uint256 c) public pure returns (uint256) { return a.add(b).sub(c); }
}
