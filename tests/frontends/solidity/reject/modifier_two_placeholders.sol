// expect-fe: FE447
// Two `_` placeholders would DUPLICATE the function body. Deferred (AG-MOD-2) — rejected.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    modifier twice() {
        _;
        _;
    }

    function setX(uint256 v) public twice {
        x = v;
    }
}
