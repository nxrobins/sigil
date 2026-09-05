// expect-fe: FE420
// Two state variables share a name. Emitting both would produce a malformed `record C { a: u256,
// a: u256 }`; the trusted compiler accepts a duplicate-field record (fail-open), so a later read
// silently resolves to one field while the other is dead = silent mis-initialization. Real solc
// rejects duplicate state vars, so only hand-crafted/invalid input reaches this, but the untrusted
// translator must reject it fail-closed. (General SOL fix surfaced by the SOL-CTOR review.)
pragma solidity ^0.8.0;
contract C {
    uint256 a;
    uint256 a;
}
