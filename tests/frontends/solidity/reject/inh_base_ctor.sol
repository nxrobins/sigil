// expect-fe: FE468
// A BASE contract declares a constructor — chaining + arg-threading base ctor bodies is deferred to
// M2, so M1 rejects fail-closed (never a silently-dropped base initializer).
pragma solidity ^0.8.0;
contract A { uint256 x; constructor() { x = 1; } }
contract B is A { uint256 y; }
