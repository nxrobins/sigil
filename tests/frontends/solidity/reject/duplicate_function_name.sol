// expect-fe: FE420
// SOL-XFILE PR3/OVL: two functions share a name AND arity (Solidity overloading distinguished only
// by parameter TYPE). Arg-count disambiguation cannot tell them apart, so SIGIL impl methods —
// which cannot share a name — would collide. Rejected fail-closed. (A DIFFERENT-arity overload IS
// now supported: it is mangled to a unique `__fe_ov{arity}_` name — see compile/overload_by_arity.)
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function setX(uint256 v) public {
        x = v;
    }

    function setX(address v) public {
        x = 0;
    }
}
