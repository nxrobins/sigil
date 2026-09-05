// expect-fe: FE441
// SOL-ACCESS EX-4: a bool-valued mapping write must be a `true`/`false` LITERAL - the
// grant/revoke idiom. A COMPUTED bool value would need a bool->u256 lowering SIGIL has
// no expression form for; fail-closed rather than a fragile statement synthesis.
pragma solidity ^0.8.0;
contract C {
    mapping(address => bool) flags;
    function set(address a, bool v) public { flags[a] = v; }
}
