// expect-fe: FE455
// cap-mode: an `onlyOwner`-shaped modifier with the WRONG operator (`!=` not `==`) — it
// gates on NOT being the owner, the opposite of the cap semantics. Not the exact gate
// shape; rejected (E-1 near-miss) rather than mis-translated.
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender != owner);
        _;
    }

    function setX(uint256 v) public onlyOwner {
        x = v;
    }
}
