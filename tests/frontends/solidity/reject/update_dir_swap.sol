// expect-fe: FE412
// SOL-UPDATE R3 (delta direction): a mint that DECREMENTS the supply (`from == 0` →
// `_totalSupply -= value`) is direction-inverted vs the canonical `_update` — `as_ts_delta`
// pins the mint branch to `+=` and the burn branch to `-=`, so the pair is not folded and the
// cross-branch writes hit the CEI gate → FE412. Folding it would corrupt the supply (MC-2).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) _balances;
    uint256 _totalSupply;

    function f(address from, address to, uint256 value) public {
        if (from == address(0)) {
            _totalSupply -= value;
        } else {
            _balances[from] -= value;
        }
        if (to == address(0)) {
            _totalSupply += value;
        } else {
            _balances[to] += value;
        }
    }
}
