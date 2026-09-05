// SOL-UNCHECKED (headline): the VERBATIM OpenZeppelin 4.x `_transfer` shape — read the balance
// into a local `fromBalance` (so the `require` message reads it once), guard, then the debit in an
// `unchecked { … }` block (a gas optimization: the `require` already proves no underflow). Part A
// (`unwrap_unchecked`) splices the `unchecked` body out — SIGIL arithmetic is always checked, so
// where Solidity WRAPS on overflow SIGIL TRAPS (fail-closed). Part B recognizes the resulting
// local-indirection debit `balances[from] = fromBalance - amount` (the local `fromBalance` aliases
// `balances[from]`, unmutated since the bind) and folds debit+credit into the ATOMIC, aliasing-safe
// `self.balances.transfer(...)`. The internal `_transfer` also inlines into `transfer` (SOL-CALLS).
// Round-trips through the trusted compiler.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;

    function _transfer(address from, address to, uint256 amount) internal {
        uint256 fromBalance = balances[from];
        require(fromBalance >= amount);
        unchecked {
            balances[from] = fromBalance - amount;
        }
        balances[to] += amount;
    }

    function transfer(address to, uint256 amount) public {
        _transfer(msg.sender, to, amount);
    }
}
