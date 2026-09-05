// EX-2 (CEI is moot in a constructor): TWO map writes (initial distribution) plus a
// `require` AFTER a state write — all sound, because the ctor builds a LOCAL record and a
// trap unwinds the whole deploy (nothing persists). The same shapes in a METHOD would be
// FE412; in a constructor they compile.
pragma solidity ^0.8.0;
contract Distributor {
    mapping(address => uint256) bal;
    uint256 total;

    constructor(address a, address b, uint256 amt) {
        bal[a] = amt;
        bal[b] = amt;
        total = amt + amt;
        require(total > 0);
    }
}
