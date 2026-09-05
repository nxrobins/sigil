// expect-fe: FE420
// SOL-HARDEN C1: a SAME-CONTRACT REDECLARED function (same name AND signature) in a MULTI-contract
// hierarchy — solc-illegal ("already declared"). This is the precise case `merge`'s dedup masks: a
// SAME-signature repeat takes the "faithful override; kept wins" branch and SILENTLY DROPS the second
// body (a different-signature repeat would instead hit the existing FE420 overload branch, so it does
// NOT exercise the masking). Inheriting `Base` makes `Main` the unique concrete sink (no FE470) while
// defeating the fast path; pre-fix the second `setX` (`x = v + 1`) is silently dropped and the contract
// translates. `reject_intra_contract_dupes` catches the duplicate name per contract → FE420.
pragma solidity ^0.8.0;

contract Base {}

contract Main is Base {
    uint256 x;

    function setX(uint256 v) public {
        x = v;
    }

    function setX(uint256 v) public {
        x = v + 1;
    }
}
