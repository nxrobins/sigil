// expect-fe: FE465
// EX-5: a constructor + cap-mode is a deferred combination. The cap-mint `new()` drops the
// owner field, so a ctor body writing it would emit a write to a non-existent field (a type
// error the FE500 parse self-check misses), and the cap E-2 dataflow gate does not scan the
// constructor. Reject; a SOL-CTOR-CAP rung does the principled merge.
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    uint256 x;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    constructor(uint256 a) {
        x = a;
    }

    function bump() public onlyOwner {
        x = x + 1;
    }
}
