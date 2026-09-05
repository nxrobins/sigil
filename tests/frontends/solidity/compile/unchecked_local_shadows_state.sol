// SOL-UNCHECKED (FE490 alpha-rename): a local declared at the TOP LEVEL of an `unchecked` block —
// here `x`, which SHADOWS the state field `x`. `unwrap_unchecked` alpha-renames the block's
// top-level locals to `__fe_unchk<N>_` on flatten, so erasing the block boundary can NEITHER leak
// the local into the enclosing scope NOR let it capture a same-named reference: the `x = 5` AFTER
// the block must resolve to the STATE field (`self.x = 5`), not the (renamed) local. The former
// FE490 reject over-approximated this — it is now translated faithfully.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function f(uint256 a) public {
        unchecked {
            uint256 x = a;
            x = x + 1;
        }
        x = 5;
    }
}
