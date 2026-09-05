// expect-fe: FE420
// SOL-EVENTS adversarial-review fold: a user function named after a Solidity elementary type
// (`payable`/`address`/`uint256`/…) is rejected. solc reserves these as keyword tokens (so this is
// invalid Solidity), but the frontend's lexer admits them as idents — and a `Call` to such a name is
// treated as a pure CAST inside a discarded `emit`, so without this gate `payable(v)` (a real,
// state-mutating call) would be silently dropped. Fail closed at the identifier gate.
pragma solidity ^0.8.0;
contract C {
    uint256 total;
    function payable(uint256 v) internal returns (uint256) { total = total + v; return v; }
    function deposit(uint256 v) public { emit Deposit(payable(v)); }
}
