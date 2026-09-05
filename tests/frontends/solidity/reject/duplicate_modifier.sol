// expect-fe: FE450
// Two modifier declarations share a name — ambiguous which body to inline.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    modifier m() {
        _;
    }

    modifier m() {
        require(x > 0);
        _;
    }

    function setX(uint256 v) public m {
        x = v;
    }
}
