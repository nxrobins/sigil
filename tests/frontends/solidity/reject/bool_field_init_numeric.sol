// expect-fe: FE445
// Adversarial-review fix: a state-field initializer must be type-checked against the
// field type at the frontend (fail-closed), not emitted as ill-typed SIGIL that only
// the trusted compiler's record-field check rescues. `bool flag = 5` is a type-kind
// mismatch with no address involved → FE445 (not FE443).
pragma solidity ^0.8.0;
contract C { bool flag = 5; function g() public view returns (bool) { return flag; } }
