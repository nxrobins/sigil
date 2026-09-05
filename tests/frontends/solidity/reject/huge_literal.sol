// expect-fe: FE430
// Fix-3: a literal >= 2^256 surfaces as the user-facing FE430 (range), not the
// internal-bug FE500 — the lexer range-checks every numeric literal up front.
pragma solidity ^0.8.0;
contract C { uint256 x = 115792089237316195423570985008687907853269984665640564039457584007913129639936; }
