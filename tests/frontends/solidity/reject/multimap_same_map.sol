// expect-fe: FE412
// SOL-MULTIMAP M-A EX-A1 (distinct map NAMES): two writes to the SAME mapping (`balances`) cannot be
// reserved-and-reordered — the two keys `a`, `b` might alias (`a == b`), which the frontend cannot
// disprove (no `a != b` analysis), and if they alias the hoisted-from-pre-write values would clobber.
// `reserve_multi_map` bails on a repeated map name → the body stays non-CEI → FE412 (the second map
// write follows the first commit). Same-map multi-write (fee-on-transfer) is the M-B milestone.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;

    function f(address a, address b, uint256 x, uint256 y) public {
        balances[a] += x;
        balances[b] += y;
    }
}
