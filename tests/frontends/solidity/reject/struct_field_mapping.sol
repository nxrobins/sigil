// expect-fe: FE461
// EX-3: a struct may hold only scalars or other structs — never a mapping (a struct is
// a value-typed record, not a bounded-container holder).
pragma solidity ^0.8.0;
contract C {
    struct S { mapping(address => uint256) balances; }
}
