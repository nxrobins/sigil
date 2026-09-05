// SOL-XFILE PR4/L3: the metadata-constructor reduction (the OZ `ERC20("Name","SYM")` shape).
// `Meta`'s constructor initializes ONLY a dropped string-metadata field (`_name`, dropped at parse),
// so it is metadata-only → dropped as a no-op. `Token`'s base-call `Meta("MyToken")` has all-literal
// args → also dropped. Token flattens to Meta's `total`+`get` plus its own `bump`, with an empty ctor.
pragma solidity ^0.8.0;

abstract contract Meta {
    string private _name;
    uint256 total;
    constructor(string memory name_) { _name = name_; }
    function get() public view returns (uint256) { return total; }
}

contract Token is Meta {
    constructor() Meta("MyToken") {}
    function bump(uint256 v) public { total = total + v; }
}
