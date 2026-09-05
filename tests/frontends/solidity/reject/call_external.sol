// expect-fe: FE401
// SOL-CALLS: a member/external call (`this.helper()`) is NOT an internal jump — only a bare
// `helper()` (a `Var` callee) inlines; a `Member` callee stays fail-closed FE401.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function helper() public view returns (uint256) {
        return x;
    }

    function f() public {
        x = this.helper();
    }
}
