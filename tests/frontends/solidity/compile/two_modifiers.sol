// Two modifiers on one function: the LEFTMOST (`onlyOwner`) is outermost, so its guard
// runs FIRST. The golden pins the inlined statement order (onlyOwner's require, then
// whenNotPaused's, then the body) — a regression in the fold direction would change it.
pragma solidity ^0.8.0;
contract C {
    address owner;
    bool paused;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    modifier whenNotPaused() {
        require(!paused);
        _;
    }

    function setX(uint256 v) public onlyOwner whenNotPaused {
        x = v;
    }
}
