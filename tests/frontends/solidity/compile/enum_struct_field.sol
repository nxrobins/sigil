// An enum + a struct that HOLDS an enum field: exercises the EX-12 `resolve_ty` threading (a
// struct field's type can be an enum name → the `u256` carrier) and the recursive
// zero-default (the struct's enum field zero-defaults to its 0th member = tag 0). A member
// literal is supplied in struct construction; a struct-field read returns the enum carrier.
pragma solidity ^0.8.0;
contract Registry {
    enum Kind { User, Admin }
    struct Entry { uint256 id; Kind kind; }
    Entry head;

    function makeAdmin(uint256 i) public pure returns (Entry memory) {
        return Entry(i, Kind.Admin);
    }

    function setHead(uint256 i) public {
        head = Entry(i, Kind.Admin);
    }

    function headKind() public view returns (Kind) {
        return head.kind;
    }
}
