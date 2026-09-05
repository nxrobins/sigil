// SOL-UNCHECKED × SOL-CAP (adversarial-review regression, was HIGH downgrade): the `onlyOwner`
// gate `require(msg.sender == owner)` wrapped in `unchecked` must STILL be recognized as the cap
// gate (emit the unforgeable `&C_Owner` borrow), NOT silently downgraded to a forgeable
// `__fe_sender == owner` trap. `unwrap_unchecked` runs BEFORE `recognize_cap_guards`, so the
// wrapped require is unwrapped first and the gate matches. The emitted SIGIL is byte-identical to
// the same contract written without the `unchecked` wrapper (pinned by the golden).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    address owner;
    modifier onlyOwner() {
        unchecked {
            require(msg.sender == owner);
        }
        _;
    }
    function credit(address a, uint256 amt) public onlyOwner {
        balances[a] = balances[a] + amt;
    }
}
