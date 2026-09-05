// expect-fe: FE412
// SOL-UPDATE R2 (the mint branch is pinned to EXACTLY `TS += value`): a custom `_update`
// override with an extra statement (here a mint counter) is NOT the canonical shape —
// `as_ts_delta` requires a single-statement branch, the pair is not folded, and the
// cross-branch writes hit the CEI gate → FE412 (fail-closed, AC-3: hooks/overrides are out).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) _balances;
    uint256 _totalSupply;
    uint256 mints;

    function f(address from, address to, uint256 value) public {
        if (from == address(0)) {
            mints = mints + 1;
            _totalSupply += value;
        } else {
            _balances[from] -= value;
        }
        if (to == address(0)) {
            _totalSupply -= value;
        } else {
            _balances[to] += value;
        }
    }
}
