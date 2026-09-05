// expect-fe: FE412
// SOL-UPDATE R4 (operand purity): every occurrence of the amount is `_balances[x]` — an `Index`
// read, not `is_transfer_operand`-pure. The four occurrences `expr_eq` each other, but an impure
// amount is not stable across the atomic op (the primitive both reads and writes the map), so the
// fold is refused and the cross-branch writes hit the CEI gate → FE412 (fail-closed).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) _balances;
    uint256 _totalSupply;

    function f(address from, address to, address x) public {
        if (from == address(0)) {
            _totalSupply += _balances[x];
        } else {
            _balances[from] -= _balances[x];
        }
        if (to == address(0)) {
            _totalSupply -= _balances[x];
        } else {
            _balances[to] += _balances[x];
        }
    }
}
