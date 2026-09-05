// expect-fe: FE454
// cap-mode (adversarial-review finding): the owner address is read as DATA (a key in a
// TWO-key write) OUTSIDE the gate. The cap model can't represent "the owner's stored
// address", and emit drops the owner field — so the E-2 field-use gate must see the
// two-key write and reject precisely (FE454), not leak a reference to a dropped field.
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    mapping(address => mapping(address => uint256)) allowance;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function adminSet(address spender, uint256 v) public onlyOwner {
        allowance[owner][spender] = v;
    }
}
