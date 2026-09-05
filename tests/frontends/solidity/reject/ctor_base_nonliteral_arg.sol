// expect-fe: FE468
// SOL-XFILE PR4/L3: a base-constructor call with a NON-LITERAL argument is not droppable — even
// though `Meta`'s ctor is metadata-only, `Meta(s)` forwards the runtime param `s`, and v1 only
// reduces ALL-LITERAL base-calls (e.g. `Meta("lit")`). Passing a computed/param value → FE468.
pragma solidity ^0.8.0;
abstract contract Meta {
    string private _n;
    constructor(string memory n) { _n = n; }
    function g() public pure returns (uint256) { return 1; }
}
contract C is Meta {
    constructor(string memory s) Meta(s) {}
}
