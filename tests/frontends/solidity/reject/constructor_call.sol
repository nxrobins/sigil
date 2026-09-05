// expect-fe: FE401
// SOL-CALLS: a bare call to a DECLARED internal function now inlines (see compile/ctor_inline_call),
// but a call to an UNKNOWN/external function stays fail-closed FE401 — including in a constructor.
pragma solidity ^0.8.0;
contract C {
    uint256 x;
    constructor() { x = notDefined(); }
}
