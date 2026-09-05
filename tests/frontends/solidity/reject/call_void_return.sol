// expect-fe: FE484
// SOL-CALLS: a statement-position void call whose callee contains a `return`. Flat inlining would
// splice that `return` into the caller (exiting it early) — a control flow Solidity never has.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function h(uint256 v) internal {
        if (v == 0) {
            return;
        }
        x = v;
    }

    function f(uint256 v) public {
        h(v);
    }
}
