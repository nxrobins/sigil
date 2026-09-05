// expect-fe: FE455
// cap-mode: a modifier that uses `msg.sender` but is NOT the exact gate shape — here a
// compound condition (`&& !paused`). Cap-translating only the identity half would silently
// drop the `!paused` check (fail-open); rejected loudly (E-1 near-miss).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    bool paused;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender == owner && !paused);
        _;
    }

    function setX(uint256 v) public onlyOwner {
        x = v;
    }
}
