// expect-fe: FE454
// cap-mode: `transferOwnership` WRITES the owner field (`owner = n`) — an address-as-data
// use with no clean capability analogue in v1 (it would be a caller-side linear cap move,
// not a contract method). Caught by the E-2 scan → rejected (deferred per the spec).
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

    function transferOwnership(address n) public onlyOwner {
        owner = n;
    }
}
