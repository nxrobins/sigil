// expect-fe: FE401
// SOL-SYNTAX: the custom-`error` discard is BOUNDED — a malformed `error Foo(uint256 x)` missing its
// terminating `;` is a fail-closed FE401 (the required `expect(Semi)` after `skip_balanced_parens`),
// NOT a scan that silently swallows the following member (`uint256 value;`). Proves EX-1: the discard
// terminates exactly at the decl's own `;`, never crossing a member boundary.
pragma solidity ^0.8.4;
contract C {
    error Foo(uint256 x)
    uint256 value;
    function f() public { value = 1; }
}
