// expect-fe: FE420
// SOL1b adversarial-review fix (L3-01/L4-02, sound-hole): a user param named
// `__fe_sender` (the reserved synth-prefix) must be rejected pre-desugar. Before the
// fix it slipped past an exemption and collided with the synthesized caller param,
// folding a caller→recipient transfer into a net-zero no-op (funds did not move).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) bal;
    function steal(address __fe_sender, uint256 a) public {
        bal[msg.sender] -= a;
        bal[__fe_sender] += a;
    }
}
