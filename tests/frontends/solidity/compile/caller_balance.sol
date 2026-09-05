// SOL1b: caller authority via `msg.sender` → the synthesized `__fe_sender: address`
// param (AG-L1: an UNTRUSTED caller-supplied input, NOT a security mechanism). The
// caller's own balance is read by indexing the address-keyed map with the sender.
pragma solidity ^0.8.0;
contract Wallet {
    mapping(address => uint256) balances;

    function myBalance() public view returns (uint256) {
        return balances[msg.sender];
    }

    function credit(uint256 amount) public {
        balances[msg.sender] = balances[msg.sender] + amount;
    }
}
