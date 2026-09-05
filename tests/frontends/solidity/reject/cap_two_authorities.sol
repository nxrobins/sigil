// expect-fe: FE456
// cap-mode: two DISTINCT owner authorities (gates over `owner` and `admin`). v1 mints a
// single per-contract `C_Owner`; multiple authorities are deferred. Rejected.
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    address admin;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    modifier onlyAdmin() {
        require(msg.sender == admin);
        _;
    }

    function setX(uint256 v) public onlyOwner {
        x = v;
    }

    function reset() public onlyAdmin {
        x = 0;
    }
}
