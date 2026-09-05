// expect-fe: FE401
// A Name(i) enum cast is the deferred explicit-cast rung (no silent ordinal leak).
pragma solidity ^0.8.0;
contract C { enum E { A, B } E s; function f() public { s = E(1); } }
