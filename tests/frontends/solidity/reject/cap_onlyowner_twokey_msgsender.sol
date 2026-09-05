// expect-fe: FE454
// cap-mode (adversarial-review finding): a guarded method whose ONLY `msg.sender` use is
// a TWO-key write. Under `onlyOwner` the gate pins `msg.sender == owner`; cap-translation
// drops the gate and frees `__fe_sender` into an untrusted caller-supplied value, so this
// `approve` would let any owner-cap holder set ANY (owner, spender) allowance — a silent
// authority weakening. The E-2 data-use gate must see the two-key write and reject (FE454).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    mapping(address => mapping(address => uint256)) allowance;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function adminApprove(address spender, uint256 v) public onlyOwner {
        allowance[msg.sender][spender] = v;
    }
}
