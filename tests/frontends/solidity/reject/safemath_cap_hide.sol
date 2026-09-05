// expect-fe: FE454
// SOL-SAFEMATH × SOL-CAP (security regression, EX-3): a SafeMath wrapper must NOT hide a guarded-body
// `msg.sender` use from the FE454 cap data-use gate. The fold runs at PARSE — before
// `recognize_cap_guards` — so `balances[msg.sender].add(x)` is already the plain
// `balances[msg.sender] + x` when the cap scan runs; the `msg.sender` data-use is visible and rejects
// exactly as it would without SafeMath (else an `&C_Owner` holder could act on any address).
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    using SafeMath for uint256;
    mapping(address => uint256) balances;
    address owner;
    modifier onlyOwner() { require(msg.sender == owner); _; }
    function credit(uint256 x) public onlyOwner {
        balances[msg.sender] = balances[msg.sender].add(x);
    }
}
