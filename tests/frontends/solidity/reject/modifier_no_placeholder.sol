// expect-fe: FE447
// A modifier with NO `_` placeholder would silently DROP the entire function body —
// catastrophic for a translator. Rejected at parse (exactly-one-`_` required).
pragma solidity ^0.8.0;
contract C {
    address owner;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender == owner);
    }

    function setX(uint256 v) public onlyOwner {
        x = v;
    }
}
