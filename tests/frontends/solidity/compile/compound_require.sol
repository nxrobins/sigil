// SOL1b: `&&` inside a `require` desugars to a bool temp + guarded `if`, then the
// SOL0 `require`→`trap_if(!(cond))` lowering applies to the temp. (Was a SOL0 FE401
// reject; `&&`/`||` are now supported via ANF desugar — short-circuit preserved.)
pragma solidity ^0.8.0;
contract C { uint256 b; function f(uint256 a) public { require(a > 0 && a < b); b = a; } }
