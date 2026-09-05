// expect-fe: FE488
// SOL1c × the SOL-CALLS FE488 class (found auditing inline_modifiers after the SOL-CALLS review): a
// host function PARAMETER (`owner`) shadows the state field the applied `onlyOwner` modifier reads. Flat
// inlining leaves the modifier's `owner` bare; emit resolves it LOCAL-first, so the inlined guard would
// read the host's ARGUMENT (`__fe_sender == owner`) instead of `self.owner` — a silent access-control
// BYPASS (an attacker calls `set(v, msg.sender)`). Rejected fail-closed; rename the parameter.
pragma solidity ^0.8.0;
contract C {
    address owner;
    uint256 val;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function set(uint256 v, address owner) public onlyOwner {
        val = v;
    }
}
