// SOL1b: `&&`/`||` ANF-desugar to a bool temp + a guarded `if`, so the RHS runs only
// on the short-circuit-reachable path (NC-L4). SIGIL has no logical operators.
pragma solidity ^0.8.0;
contract Guards {
    function inRange(uint256 x) public pure returns (bool) {
        return x > 0 && x < 100;
    }

    function either(uint256 a, bool flag) public pure returns (uint256) {
        if (a > 10 || flag) {
            return 1;
        }
        return 0;
    }
}
