// expect-fe: FE412
// SOL-UPDATE R1 (the debit guard is pinned to `<`): the 5.x insufficient-balance guard must be
// EXACTLY `if (fb < value) revert`. An off-by-one `<=` guard is a DIFFERENT program (it reverts on
// an exact-balance transfer, which `erc20_update` would allow) — `as_update_debit` does not match
// it, the if-pair is not folded, and the cross-branch writes hit the CEI gate → FE412.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) _balances;
    uint256 _totalSupply;

    function f(address from, address to, uint256 value) public {
        if (from == address(0)) {
            _totalSupply += value;
        } else {
            uint256 fb = _balances[from];
            if (fb <= value) {
                revert();
            }
            _balances[from] = fb - value;
        }
        if (to == address(0)) {
            _totalSupply -= value;
        } else {
            _balances[to] += value;
        }
    }
}
