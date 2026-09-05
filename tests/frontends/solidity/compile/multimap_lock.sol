// SOL-MULTIMAP M-A: a lock/unlock body — two writes to DISTINCT mappings (`balances` and `locked`).
// FE412-blocked before this rung (the first map write commits, the second is a trap-capable op after a
// commit; SIGIL has no rollback). Because the two maps are different storage (provably distinct — no
// `a != b` proof needed), `reserve_multi_map` folds them into an atomic reserve-all-then-write batch:
// hoist both values (read pre-write), `reserve1` both maps (read-only), then both `insert`s trap-free.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;
    mapping(address => uint256) locked;

    function lock(address u, uint256 a) public {
        balances[u] -= a;
        locked[u] += a;
    }
}
