// expect-fe: FE412
// SOL-MULTIMAP M-A adversarial-review CRITICAL regression: a plain write's insert KEY that READS a map
// the batch writes must bail. The value is hoisted (snapshotted pre-write), but the KEY is re-emitted
// verbatim in the deferred insert, which lands AFTER the reordered-to-middle transfer — so
// `ledger[balances[to]]` would be re-evaluated POST-transfer and write the WRONG slot (source: pre-transfer
// balances[to]; SIGIL would use post-transfer). `reserve_multi_map` bails on any impure (`Index`-bearing)
// key → the body stays non-CEI → FE412 (mirrors the transfer's own `is_transfer_operand` operand guard).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    mapping(uint256 => uint256) ledger;

    function f(address from, address to, uint256 amt) public {
        ledger[balances[to]] = 5;
        balances[from] -= amt;
        balances[to] += amt;
    }
}
