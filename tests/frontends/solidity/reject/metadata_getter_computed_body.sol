// expect-fe: FE410
// SOL-XFILE PR5/L4: the metadata-getter drop is TIGHT — it fires ONLY on a body that is EXACTLY
// `return <ident>;`. This getter has an extra statement, so it is NOT a recognized metadata getter,
// is NOT dropped, and its `string` return type reaches check → FE410 (fail-closed). Pins that a
// fancier `string`-returning public function is not silently swallowed.
pragma solidity ^0.8.0;
contract C {
    string private _name;

    function name() public view returns (string memory) {
        uint256 n = 1;
        return _name;
    }
}
