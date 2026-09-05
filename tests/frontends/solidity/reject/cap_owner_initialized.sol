// expect-fe: FE454
// Review finding 2: the owner field has a fixed initializer (a pinned address). A capability
// cannot represent "owner is this specific address" — cap-translation would silently drop the
// literal and grant authority to whoever holds the minted cap. Rejected; keep the address
// model. (A NON-initialized owner = the canonical "deployer becomes owner" → the minted
// C_Owner returned from new() is that authority.)
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner = 0x1234;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function setX(uint256 v) public onlyOwner {
        x = v;
    }
}
