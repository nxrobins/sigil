// expect-fe: FE441
// EX-6: a `uintN`-valued mapping is deferred — the bounded map is u256-valued and traps
// only at 2^256, so a uintN credit exceeding 2^N would NOT trap (the HOLE-1 existential).
// v1 admits uintN only as a scalar type.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint8) m;
}
