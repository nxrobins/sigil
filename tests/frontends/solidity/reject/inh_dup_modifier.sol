// expect-fe: FE450
// SOL-HARDEN C1: a SAME-CONTRACT duplicate modifier in a MULTI-contract hierarchy. Inheriting `Base`
// makes `Main` the unique concrete sink (no FE470) while defeating the single-concrete-NO-bases fast
// path, so flatten's `merge` runs and its name-keyed derived-wins dedup would silently collapse the two
// `m`s — keeping the FIRST (no-op) body and compiling `setX` with a vanished guard.
// `reject_intra_contract_dupes` catches it per contract → FE450 (the same code the single-contract fast
// path already yields via inline_modifiers).
pragma solidity ^0.8.0;

contract Base {}

contract Main is Base {
    uint256 x;

    modifier m() {
        _;
    }

    modifier m() {
        require(x > 0);
        _;
    }

    function setX(uint256 v) public m {
        x = v;
    }
}
