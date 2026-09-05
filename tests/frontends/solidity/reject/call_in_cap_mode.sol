// expect-fe: FE487
// SOL-CALLS x SOL-CAP: an internal call under cap-mode. The cap E-2/H7 data-use gate runs BEFORE
// inlining and cannot see a `msg.sender`/owner use hidden in a callee body (`log[_msgSender()]`
// bypasses FE454), so the combination is rejected fail-closed.
// sigil:cap-access-control
pragma solidity ^0.8.0;
contract C {
    address owner;
    mapping(address => uint256) log;

    modifier onlyOwner() {
        require(msg.sender == owner);
        _;
    }

    function _msgSender() internal view returns (address) {
        return msg.sender;
    }

    function logCaller() public onlyOwner {
        log[_msgSender()] = 1;
    }
}
