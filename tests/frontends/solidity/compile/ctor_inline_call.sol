// SOL-CALLS: a constructor calling a DECLARED internal function inlines it — a single-`return`
// `_initial()` folds to its value in the ctor's build-and-return, and it round-trips. (The bare
// `_initial()` is an internal jump, inlined; `this._initial()` would be an external call → FE401.)
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function _initial() internal pure returns (uint256) {
        return 42;
    }

    constructor() {
        x = _initial();
    }
}
