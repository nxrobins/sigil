// SOL-HARDEN C1 (EX-1): a GENUINE cross-contract function override — `B.setX` overrides `A.setX`
// (same signature, `virtual`/`override` keywords). One `setX` per contract, so
// `reject_intra_contract_dupes` must NOT flag it; `merge` dedups derived-wins, keeping B's body
// (`x = v + 1`). Proves the C1 fix rejects only WITHIN-one-contract duplicates, never a legal override.
pragma solidity ^0.8.0;

contract A {
    uint256 x;

    function setX(uint256 v) public virtual {
        x = v;
    }
}

contract B is A {
    function setX(uint256 v) public override {
        x = v + 1;
    }
}
