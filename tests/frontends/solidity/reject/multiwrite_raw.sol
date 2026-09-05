// expect-fe: FE412
// SOL-MULTIWRITE EX-1 (no RAW): the transform must NOT reorder a body where a later write READS a
// storage slot an earlier statement WROTE — moving all reads before all writes would make that read
// see the stale (pre-write) value. Here `total` is written, then read into the map-write RHS
// (`total + 1`) → a read-after-write hazard → `total_cei` bails → the body stays non-CEI → FE412 (the
// map write follows the committed `total` write). Without the RAW guard the reorder would compute
// `balances[a] = total_old + 1` instead of the source's `total_new(=x) + 1`.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    uint256 total;

    function f(address a, uint256 x) public {
        total = x;
        balances[a] = total + 1;
    }
}
