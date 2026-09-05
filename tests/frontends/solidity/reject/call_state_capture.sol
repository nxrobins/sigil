// expect-fe: FE488
// SOL-CALLS (adversarial review): a callee's state-field reference (`ownerAddr` returns state `owner`)
// captured by a caller PARAM of the same name. Un-fixed, the inlined guard read the attacker-supplied
// `owner` argument instead of `self.owner` (an access-control bypass). Fail-closed: rename the param.
pragma solidity ^0.8.0;
contract C {
    address owner;
    uint256 secret;

    function ownerAddr() internal view returns (address) {
        return owner;
    }

    function admin(address owner) public {
        require(msg.sender == ownerAddr());
        secret = 1;
    }
}
