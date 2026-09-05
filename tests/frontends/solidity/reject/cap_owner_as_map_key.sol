// expect-fe: FE454
// cap-mode: the owner address is read as DATA (used as a map key). The cap model can't
// represent "the owner's stored address"; rejected (E-2).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    mapping(address => uint256) bal;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function credit(uint256 v) public onlyOwner {
        bal[owner] = v;
    }
}
