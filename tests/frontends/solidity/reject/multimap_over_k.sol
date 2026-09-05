// expect-fe: FE412
// SOL-MULTIMAP M-A EX-A4 (≤4 distinct maps): a body touching >4 distinct mappings exceeds the dumb
// reservation-prefix bound. `reserve_multi_map` bails on >4 maps → the body stays non-CEI → FE412 (the
// second map write follows the first commit). A larger batch is a declared anti-goal (unbounded fan-out).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) a;
    mapping(address => uint256) b;
    mapping(address => uint256) c;
    mapping(address => uint256) d;
    mapping(address => uint256) e;

    function f(address k) public {
        a[k] += 1;
        b[k] += 1;
        c[k] += 1;
        d[k] += 1;
        e[k] += 1;
    }
}
