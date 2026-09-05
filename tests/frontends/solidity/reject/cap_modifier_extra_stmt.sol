// expect-fe: FE455
// cap-mode: an `onlyOwner`-shaped modifier with an EXTRA statement before `_` (not the
// exact `require(msg.sender == owner); _;`). The extra guard would be silently dropped by
// a bare cap gate; rejected (E-1 near-miss).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender == owner);
        require(x > 0);
        _;
    }

    function setX(uint256 v) public onlyOwner {
        x = v;
    }
}
