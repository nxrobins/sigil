// SOL-DIVERGE (EX-1 boundary): the three UNCONDITIONAL abort idioms all lower to the divergent `trap()`.
// `require(false)` / `assert(false)` are literal-false aborts; `revert()` always aborts. As the sole
// body of a VALUE-returning function each satisfies the return checker (the T044 fix — a Unit
// `trap_if(true)`/`trap_if(!(false))` here would leave the function returnless). A NON-constant
// `require(c)` is NOT one of these — it stays the conditional `trap_if(!(c))` (see the golden tests).
pragma solidity ^0.8.0;
contract Guards {
    function disabled() public pure returns (uint256) {
        require(false, "disabled");
    }

    function unreachable() public pure returns (uint256) {
        assert(false);
    }

    function notImplemented() public pure returns (uint256) {
        revert("not implemented");
    }
}
