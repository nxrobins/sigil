// expect-fe: FE484
// SOL-ACCESS PR5-W4: only TAIL-position pure returns drop. A NON-tail early return
// (`if (v>0){ return v; } x=v; return 0;` — the first return is mid-body control flow)
// cannot be modeled by flat inlining and stays FE484 when called as a statement.
pragma solidity ^0.8.0;
contract C {
    uint256 x;
    function helper(uint256 v) internal returns (uint256) {
        if (v > 0) { return v; }
        x = v;
        return 0;
    }
    function f(uint256 v) public { helper(v); }
}
