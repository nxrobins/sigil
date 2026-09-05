// expect-fe: FE413
// A NON-literal state-field initializer is still rejected even WITH a constructor — emit only
// seeds the record literal with literals, and cannot evaluate a computed init there. (Move
// the initializer into the constructor body instead — a documented anti-goal.)
pragma solidity ^0.8.0;
contract C {
    uint256 x = 1 + 1;
    constructor(uint256 a) { x = a; }
}
