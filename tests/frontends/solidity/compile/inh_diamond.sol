// SOL-INH M1: the OpenZeppelin Context diamond — D is A,B; A is Ctx; B is Ctx. C3 linearizes to
// [D,B,A,Ctx]; state lays out most-base-first as [ctx,a,b,d], the shared Ctx field appearing ONCE.
pragma solidity ^0.8.0;

contract Ctx {
    uint256 ctx;
}

contract A is Ctx {
    uint256 a;
}

contract B is Ctx {
    uint256 b;
}

contract D is A, B {
    uint256 d;

    function setD(uint256 v) public {
        d = v;
    }
}
