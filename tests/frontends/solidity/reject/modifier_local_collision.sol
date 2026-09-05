// expect-fe: FE449
// A modifier-introduced local (`t`) collides with a host function local (`t`). Inlining
// would silently shadow it (a semantic change); rejected rather than alpha-renamed.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    modifier withTemp() {
        uint256 t = 1;
        require(t > 0);
        _;
    }

    function setX(uint256 v) public withTemp {
        uint256 t = v;
        x = t;
    }
}
