// expect-fe: FE449
// A modifier declares a local (`owner`) whose name equals a STATE FIELD. Flat inlining
// merges the scopes, so after splicing the local would shadow the state field — the host
// body's `owner = v` would write the dead local, NOT `self.owner` (a verified-but-wrong
// translation). The collision gate seeds on state fields too, so this is rejected (FE449).
pragma solidity ^0.8.0;
contract C {
    uint256 owner;

    modifier check() {
        uint256 owner = 5;
        require(owner == 5);
        _;
    }

    function setOwner(uint256 v) public check {
        owner = v;
    }
}
