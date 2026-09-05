// expect-fe: FE410
// SOL-ACCESS EX-3: `bytes16` — like every `bytesN` for N<32 — is left-aligned and
// unmodeled; only whole `bytes32` is admitted. Rejected fail-closed (FE410), never
// silently carried in a right-aligned u256.
pragma solidity ^0.8.0;
contract C { bytes16 half; }
