// A guard-only modifier that reads a bool state field (the `whenNotPaused` pattern).
// No `msg.sender`, so no caller-authority param is synthesized — the inlined guard is a
// plain `require(!paused)` lowered to a `trap_if`.
pragma solidity ^0.8.0;
contract C {
    bool paused;
    uint256 x;

    modifier whenNotPaused() {
        require(!paused);
        _;
    }

    function setX(uint256 v) public whenNotPaused {
        x = v;
    }
}
