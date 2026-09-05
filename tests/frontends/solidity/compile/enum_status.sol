// A contract exercising enums: an `enum` decl (3 members; source order = the 0-based tag),
// an enum-typed status field (zero-default = the 0th member, tag 0), member-literal
// assignment, an `==` compare and an ordered `<` compare (Solidity enums ARE ordered), an
// enum-typed param, a same-enum assignment, and an enum-typed return. The enum lowers to a
// `u256` tag carrier and the decl is erased — the trusted compiler sees only `u256`.
pragma solidity ^0.8.0;
contract Workflow {
    enum State { Pending, Active, Closed }
    State status;
    uint256 count;

    function activate() public {
        status = State.Active;
    }

    function close() public {
        status = State.Closed;
    }

    function isActive() public view returns (bool) {
        return status == State.Active;
    }

    function before(State other) public view returns (bool) {
        return status < other;
    }

    function reset(State s) public {
        status = s;
    }

    function current() public view returns (State) {
        return status;
    }
}
