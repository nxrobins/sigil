// expect-fe: FE489
// SOL-CALLS (adversarial review): a param-bearing value-call inside a `||` short-circuit operand. Its
// arg let-prelude (`a - b`, a trap-capable subtraction) would hoist OUT of the guard and evaluate on the
// `flag == true` path Solidity skips — Solidity returns 42, the naive inline would trap. Fail-closed.
pragma solidity ^0.8.0;
contract C {
    function _id(uint256 x) internal pure returns (uint256) {
        return x;
    }

    function act(bool flag, uint256 a, uint256 b) public pure returns (uint256) {
        require(flag || _id(a - b) > 0);
        return 42;
    }
}
