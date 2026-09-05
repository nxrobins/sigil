// sigil:cap-access-control
// SOL-CAP headline: `onlyOwner` → an UNFORGEABLE `&C_Owner` gate (no forgeable
// `__fe_sender == owner` trap). `new()` mints the root owner cap and returns it; the owner
// address field is dropped (it was used purely as the gate). A caller without the cap
// cannot compile a call to `setX`.
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
}
