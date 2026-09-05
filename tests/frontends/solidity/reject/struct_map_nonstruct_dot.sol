// expect-fe: FE441
// SOL-ACCESS: a `var[key].field` path whose base is NOT a mapping-to-struct (here a
// plain uint256 map) - the parse rewrite minted a synthesized name no explode matched;
// the sweep rejects it precisely (fail-closed, MC-4's cousin: no phantom slot).
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) balances;
    function f(address a) public view returns (uint256) { return balances[a].total; }
}
