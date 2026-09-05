// expect-fe: FE412
// SOL-MULTIMAP M-B AC-B1 (debit + EXACTLY 2 credits): an N-way split (a debit + THREE credits) is out of
// scope — `transfer_split` takes exactly 3 addresses. `recognize_split` folds the debit + first 2 credits
// into a `MapSplitTransfer`; the 3rd credit is a SEPARATE same-map write after the committed split → FE412
// (fail-closed). A variadic split needs a primitive SIGIL's fixed arity lacks.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;

    function f(address a, address b, address c, uint256 amount, uint256 x, uint256 y, uint256 z) public {
        balances[msg.sender] -= amount;
        balances[a] += x;
        balances[b] += y;
        balances[c] += z;
    }
}
