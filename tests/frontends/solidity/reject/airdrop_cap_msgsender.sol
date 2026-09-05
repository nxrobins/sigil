// expect-fe: FE454
// SOL-AIRDROP Correction B (the security proof): in cap-mode the ONLY `msg.sender` use lives
// INSIDE the airdrop loop body. The SOL-CAP scanner (`stmt_uses_msg_sender`) MUST recurse the
// `AirdropLoop` node — not hit its `_ => false` catch-all — to see it; else this owner-identity
// body-use escapes the E-2 gate, cap-mode proceeds, and the authority gate silently drops (the
// method would take the forgeable `__fe_sender` as a free param). The airdrop's `from = msg.sender`
// is exactly such a use → FE454.
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    mapping(address => uint256) balances;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function _transfer(address from, address to, uint256 amount) internal {
        balances[from] -= amount;
        balances[to] += amount;
    }

    function airdrop(address[] calldata recipients, uint256[] calldata amounts) external onlyOwner {
        for (uint256 i = 0; i < recipients.length; i++) {
            _transfer(msg.sender, recipients[i], amounts[i]);
        }
    }
}
