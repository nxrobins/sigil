// expect-fe: FE402
// SOL-CALLS (adversarial review): a fan-out call graph. Each f_i calls f_{i+1} TWICE, so the
// inlined output is exponential (2^13) even though the recursion DEPTH (13) is under the cap and
// the nesting stays flat. The total-expansion cap rejects it (bounds SIZE, not just depth).
pragma solidity ^0.8.0;
contract C { uint256 x;
    function f0() internal { f1(); f1(); }
    function f1() internal { f2(); f2(); }
    function f2() internal { f3(); f3(); }
    function f3() internal { f4(); f4(); }
    function f4() internal { f5(); f5(); }
    function f5() internal { f6(); f6(); }
    function f6() internal { f7(); f7(); }
    function f7() internal { f8(); f8(); }
    function f8() internal { f9(); f9(); }
    function f9() internal { f10(); f10(); }
    function f10() internal { f11(); f11(); }
    function f11() internal { f12(); f12(); }
    function f12() internal { f13(); f13(); }
    function f13() internal { x = 1; }
    function go() public { f0(); } }
