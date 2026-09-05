// expect-fe: FE453
// A `nonReentrant`-style modifier puts the unlock (`locked = false`) AFTER `_` — a suffix.
// In Solidity a suffix runs on function EXIT (even after a body `return`); flat inlining
// can't model that — the unlock would become dead code when the body returns, leaving the
// lock stuck (the contract bricked). SOL1c requires `_` in tail position and rejects the
// suffix (FE453) — the fundamental reason a lock-wrap modifier can't be faithfully inlined.
pragma solidity ^0.8.0;
contract C {
    bool locked;
    uint256 x;

    modifier nonReentrant() {
        require(!locked);
        locked = true;
        _;
        locked = false;
    }

    function setX(uint256 v) public nonReentrant {
        require(v > 0);
        x = v;
    }
}
