// SOL-UNCHECKED (FE490 alpha-rename, adversarial-review F1): a top-level local inside an
// `unchecked` block that is itself nested inside an `if` branch — the realistic guarded-debit-in-a-
// conditional pattern the old FE490 reject forfeited. `unwrap_unchecked` alpha-renames the local
// (`__fe_unchk<N>_x`) and splices it into the surviving `if { … }` block, where it is correctly
// scoped. Translates + round-trips.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;

    function credit(address a, uint256 amount) public {
        if (amount > 0) {
            unchecked {
                uint256 x = balances[a];
                balances[a] = x + amount;
            }
        }
    }
}
