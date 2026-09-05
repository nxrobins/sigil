// expect-fe: FE454
// cap-mode: the owner address is compared OUTSIDE the gate (an `isOwner` view). A second
// identity comparison has no capability analogue (a cap is unforgeable possession, not a
// comparable value); rejected (E-2).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function setX(uint256 v) public onlyOwner {
        x = v;
    }

    function isOwner(address a) public view returns (bool) {
        return a == owner;
    }
}
