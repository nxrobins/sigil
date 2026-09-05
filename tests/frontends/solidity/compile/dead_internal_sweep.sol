// SOL-XFILE PR5/L4: the dead-internal sweep. After `inline_internal_calls` splices every call to a
// contract function, an `internal`/`private` function with ZERO remaining call sites is DROPPED —
// MORE faithful (internal fns are not part of Solidity's external ABI, and the trusted compiler
// forces every emitted impl method `Public`, so a retained internal WIDENS the surface) and REQUIRED
// for OZ (`Context._msgData(): bytes` rides in via a base, is uncalled, and would be a hard FE410).
// Here `_meta()` returns `bytes` (out of subset) but is NEVER called → swept before check (no
// FE410); `_helper` IS called → inlined into `bump`, then swept. Only the public `bump`/`get`
// survive to emit.
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function _meta() internal view returns (bytes memory) {
        return msg.data;
    }

    function _helper(uint256 v) internal pure returns (uint256) {
        return v + 1;
    }

    function bump(uint256 v) public {
        x = _helper(v);
    }

    function get() public view returns (uint256) {
        return x;
    }
}
