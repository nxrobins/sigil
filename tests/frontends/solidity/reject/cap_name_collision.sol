// expect-fe: FE457
// cap-mode: a user function named `C_Owner` collides with the synthesized cap-type name
// `{Contract}_Owner`. A duplicate top-level name is N002 at name-resolution — invisible to
// the FE500 parse self-check — so the frontend must catch it (IMPL-3).
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

    function C_Owner() public view returns (uint256) {
        return x;
    }
}
