// SOL-MULTIWRITE regression (adversarial-review CRITICAL fix): a TRAP-FREE scalar store that reads
// the map, sitting BEFORE the map write in source, must observe the PRE-write map value. `total_cei`
// hoists EVERY scalar store's RHS into the pre-write prefix (not just trap-capable ones), so
// `snapshot` reads `balances[account]` BEFORE the credit commits. Before the fix, the trap-free store
// was moved AS-IS to after the reordered-to-front map write and read the POST-write value (snapshot =
// 105 instead of 100 for a +5 credit) — a silent mistranslation. Now: `let __fe_w0 = balances[account]`
// precedes the `insert`, and `snapshot = __fe_w0`.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;
    uint256 snapshot;

    function creditAndSnapshot(address account, uint256 amount) public {
        snapshot = balances[account];
        balances[account] += amount;
    }
}
