// expect-fe: FE454
// cap-mode: the owner address is also exposed as data (a getter returns it). A capability
// is opaque — it has no readable address — so an address used as BOTH a gate and data
// diverges observably from the cap model. Rejected (keep the address model instead).
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

    function getOwner() public view returns (address) {
        return owner;
    }
}
