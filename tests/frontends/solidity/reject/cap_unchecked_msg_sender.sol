// expect-fe: FE454
// SOL-UNCHECKED × SOL-CAP (adversarial-review regression, was CRITICAL authority-widening): an
// `unchecked` wrapper must NOT hide a guarded-body `msg.sender` use from the FE454 cap data-use
// gate. `unwrap_unchecked` runs BEFORE `recognize_cap_guards`, so the wrapped `balances[msg.sender]`
// use is visible and rejects EXACTLY as the unwrapped form does. If it slipped through, cap-mode
// would drop the gate and hand the method the untrusted caller-supplied `__fe_sender` as a free
// param — any `&C_Owner` holder could then credit/mutate ANY account.
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    address owner;
    modifier onlyOwner() { require(msg.sender == owner); _; }
    function credit(uint256 amount) public onlyOwner {
        unchecked {
            balances[msg.sender] = balances[msg.sender] + amount;
        }
    }
}
