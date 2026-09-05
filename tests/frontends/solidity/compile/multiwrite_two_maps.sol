// SOL-MULTIMAP M-A: two INDEPENDENT map writes to DISTINCT mappings (`a[k] = x; b[k] = x;`). This was
// an FE412 reject under SOL-MULTIWRITE (which bailed on ≥2 map writes), but M-A now handles it soundly:
// different map NAMES are provably distinct storage (no `a != b` key-distinctness proof needed), so the
// two writes fold into an atomic reserve-all-then-write batch. (Plain `= x` writes — no compound arith —
// exercise the op-`Eq` hoist path, complementing `multimap_lock`'s compound `+=`/`-=`.)
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) a;
    mapping(address => uint256) b;

    function f(address k, uint256 x) public {
        a[k] = x;
        b[k] = x;
    }
}
