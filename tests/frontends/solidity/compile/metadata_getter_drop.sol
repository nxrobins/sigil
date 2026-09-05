// SOL-XFILE PR5/L4: the metadata-getter drop. A PUBLIC `returns (string)` view whose body is
// EXACTLY `return <ident>;` (the OZ `name()`/`symbol()` shape) is DROPPED — the string state field
// was dropped at parse and a `string` return is unrepresentable (FE410), so the faithful lowering is
// nothing. `decimals()` (uint8, `return 18`) and `balanceOf` are NOT string getters → KEPT.
pragma solidity ^0.8.0;
contract Token {
    mapping(address => uint256) balances;
    string private _name;
    string private _symbol;

    function name() public view returns (string memory) {
        return _name;
    }

    function symbol() public view returns (string memory) {
        return _symbol;
    }

    function decimals() public pure returns (uint8) {
        return 18;
    }

    function balanceOf(address a) public view returns (uint256) {
        return balances[a];
    }
}
