// SOL-MULTIWRITE: the OZ `_mint` shape — a scalar-then-map multi-write (the `totalSupply` bump then
// the balance credit), in the compound `+=` form. FE412-blocked before this rung (the `totalSupply`
// write commits, then the map write is a trap-capable op after a commit). `total_cei` hoists the
// `totalSupply` arithmetic into `__fe_w0` and reorders the compound map write first (as the first
// write, its own overflow/capacity trap is rollback-moot), leaving a trap-free `totalSupply` store.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;
    uint256 totalSupply;

    function mint(address account, uint256 amount) public {
        totalSupply += amount;
        balances[account] += amount;
    }
}
