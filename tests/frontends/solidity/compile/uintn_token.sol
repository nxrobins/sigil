// Per-width uintN: a `uint8 decimals` getter/setter, a `uint128` accumulator doing checked
// `+`/`*` (the width-trap rides the emitted `__fe_{add,mul}_checked` helpers), WIDENING
// uint128 → uint256, a uintN comparison, and a `uint128` STRUCT field read/write/arith.
pragma solidity ^0.8.0;
contract UToken {
    struct Packed { uint128 lo; uint128 hi; }
    uint8 dec;
    uint128 supply;
    Packed slot;

    function decimals() public view returns (uint8) {
        return dec;
    }

    function setDecimals(uint8 d) public {
        dec = d;
    }

    function mint(uint128 a) public {
        supply = supply + a;
    }

    function scale(uint128 k) public {
        supply = supply * k;
    }

    function widened() public view returns (uint256) {
        return supply;
    }

    function below(uint128 lim) public view returns (bool) {
        return supply < lim;
    }

    function bumpLo(uint128 d) public {
        slot.lo = slot.lo + d;
    }
}
