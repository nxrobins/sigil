// expect-fe: FE482
// SIGIL has no `**`; only a literal-base/literal-exponent `**` constant-folds. A variable exponent
// (`x ** 2`, `10 ** decimals`) can't be folded → fail closed.
pragma solidity ^0.8.0;
contract C { function f(uint256 x) public pure returns (uint256) { return x ** 2; } }
