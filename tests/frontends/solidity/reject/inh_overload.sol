// expect-fe: FE420
// An inherited OVERLOAD — `f(address)` in the derived vs `f(uint256)` in the base (same name,
// genuinely different signature). SIGIL methods don't overload, so this is rejected fail-closed
// rather than silently collapsed to one method (which would drop a function from the ABI).
pragma solidity ^0.8.0;
contract Base { uint256 z; function f(uint256 a) public { z = a; } }
contract Derived is Base { function f(address a) public { z = 1; } }
