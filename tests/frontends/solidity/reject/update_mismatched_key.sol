// expect-fe: FE412
// SOL-UPDATE R5 (key identity): the credit writes a THIRD address (`other`), not the `to` the
// burn test dispatched on — the fold requires the debit key ≡ the mint test's `from` and the
// credit key ≡ the burn test's `to` (`expr_eq`), so this different program is not folded and
// the cross-branch writes hit the CEI gate → FE412. Folding it would misdirect the credit (MC-1).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) _balances;
    uint256 _totalSupply;

    function f(address from, address to, address other, uint256 value) public {
        if (from == address(0)) {
            _totalSupply += value;
        } else {
            _balances[from] -= value;
        }
        if (to == address(0)) {
            _totalSupply -= value;
        } else {
            _balances[other] += value;
        }
    }
}
