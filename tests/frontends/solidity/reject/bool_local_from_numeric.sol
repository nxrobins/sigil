// expect-fe: FE445
// Adversarial-review fix: a non-address type mismatch (`bool x = 5`) reports the
// dedicated type-mismatch code FE445, NOT the address-misuse code FE443 (which is
// reserved for genuine address↔uint256 confusion). The reject was always correct;
// the FE-code is now precise.
pragma solidity ^0.8.0;
contract C { function f() public pure returns (bool) { bool x = 5; return x; } }
