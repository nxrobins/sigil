// expect-fe: FE475
// SOL-XFILE PR2/L2: an abstract `virtual` method that NO contract in the linearization implements
// survives the derived-wins merge with no body → FE475 (the flattened concrete is itself abstract
// and cannot emit). An OVERRIDDEN bodiless would be dropped (the bodied derived wins) — this one is
// never overridden, so it fails closed rather than emitting a bodiless function.
pragma solidity ^0.8.0;
abstract contract A { function mustImpl() external virtual returns (uint256); }
contract B is A { uint256 y; }
