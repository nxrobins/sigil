// SOL-XFILE PR3/OVL: a same-name overload distinguished by ARITY (the OZ `_approve` 3-arg/4-arg
// shape) is disambiguated — each definition is renamed to a unique `__fe_ov{arity}_{name}` and every
// call site is rewritten by argument count. Here the 1-arg `bump` (a pure helper) is called TWICE in
// EXPRESSION position from the 2-arg `bump`; both calls rewrite to the mangled 1-arg method (then
// inline). (A same-ARITY overload stays FE420 — see reject/duplicate_function_name.)
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function bump(uint256 v) public view returns (uint256) {
        return v + 1;
    }

    function bump(uint256 v, uint256 w) public {
        x = bump(v) + bump(w);
    }
}
