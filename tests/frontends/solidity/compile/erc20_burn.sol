// SOL-MULTIWRITE: the verbatim OZ 4.x `_burn` shape — a straight-line multi-write body (the balance
// debit + the `totalSupply` decrement) that FE412-blocked before this rung, because SIGIL has no
// rollback (the balance write commits, then the trap-capable `totalSupply` arithmetic runs). The
// `total_cei` desugar pass HOISTS the `totalSupply` arithmetic into a pre-write `__fe_w0` local and
// REORDERS the single map write first, so every trapping computation runs before any commit and the
// only store after the map write is trap-free — a form the UNCHANGED FE412 gate accepts. Faithful to
// Solidity: on any trap (an underflow), NOTHING commits, matching a revert. (Was
// `reject/unchecked_multi_write.sol`, expect-fe FE412, until this rung.)
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;
    uint256 totalSupply;

    function burn(address from, uint256 amount) public {
        uint256 fromBalance = balances[from];
        require(fromBalance >= amount);
        unchecked {
            balances[from] = fromBalance - amount;
            totalSupply = totalSupply - amount;
        }
    }
}
