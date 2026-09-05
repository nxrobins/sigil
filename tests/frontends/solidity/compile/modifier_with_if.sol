// The `_` placeholder nested inside a modifier's `if` (a conditional "feature flag"
// modifier): the body splices into the branch, so it runs only when `active`. Proves the
// splice is positional (descends into `if` branches), not just top-level.
pragma solidity ^0.8.0;
contract C {
    bool active;
    uint256 x;

    modifier whenActive() {
        if (active) {
            _;
        }
    }

    function setX(uint256 v) public whenActive {
        x = v;
    }
}
