// expect-fe: FE454
// SOL-UNCHECKED × SOL-CAP (adversarial-review regression, was HIGH): an `unchecked` wrapper must
// NOT hide a use of the access-controlling `owner` field OUTSIDE the gate from the E-2
// `check_field_only_in_gate` scan. `unwrap_unchecked` runs BEFORE `recognize_cap_guards`, so the
// wrapped `balances[owner]` data-use is visible and rejects FE454 (an opaque `&C_Owner` cap has no
// readable address; emitting cap-mode SIGIL that references `owner` as data would dangle).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    address owner;
    modifier onlyOwner() { require(msg.sender == owner); _; }
    function credit(uint256 amt) public onlyOwner {
        unchecked {
            balances[owner] = balances[owner] + amt;
        }
    }
}
