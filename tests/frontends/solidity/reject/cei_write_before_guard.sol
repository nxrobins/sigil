// expect-fe: FE412
// The CEI synergy WITHOUT a suffix: a modifier writes state BEFORE `_` (no trailing code),
// and the guarded body then runs a trap-capable op (a `require`). Inlined, the guard runs
// AFTER the committed state write — and SIGIL's trap has no atomic rollback, so a body trap
// would leave the bump committed. The existing CEI checker rejects FE412 by construction.
pragma solidity ^0.8.0;
contract C {
    uint256 count;
    uint256 total;

    modifier bump() {
        count = count + 1;
        _;
    }

    function add(uint256 a) public bump {
        require(a > 0);
        total = total + a;
    }
}
