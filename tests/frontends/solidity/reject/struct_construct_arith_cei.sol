// expect-fe: FE412
// adversarial-review (CEI bypass via construction): trap-capable arithmetic HIDDEN inside
// a struct construction arg, AFTER a storage write. `amt - fee` can underflow-trap after
// `balance[user]` has already committed; a SIGIL trap does NOT roll back the prior write,
// but Solidity's revert would — a silent weakening. The CEI gate must descend into the
// construction's args (FE412), not treat the whole `Call` as arithmetic-free.
pragma solidity ^0.8.0;
contract Ledger {
    struct Receipt { uint256 net; uint256 ts; }
    mapping(address => uint256) balance;
    Receipt last;

    function credit(address user, uint256 amt, uint256 fee) public {
        balance[user] = amt;
        last = Receipt(amt - fee, 0);
    }
}
