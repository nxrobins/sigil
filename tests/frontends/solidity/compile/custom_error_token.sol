// SOL-SYNTAX: modern (Solidity ≥0.8.4) custom `error` declarations at BOTH file scope and
// contract-member scope are DISCARDED — the frontend lowers every `revert CustomError(...)` to an
// unconditional `trap()` (SOL-DIVERGE), dropping the name + args, so a custom-error DECLARATION
// carries no information the translation uses. The contract then translates end-to-end.
pragma solidity ^0.8.4;

// File-level custom error (discarded).
error Unauthorized(address caller);

contract Guarded {
    uint256 value;

    // Contract-member custom error (discarded).
    error TooSmall(uint256 given);

    function setValue(uint256 v) public {
        if (v == 0) {
            revert TooSmall(v);
        }
        value = v;
    }

    function check(address who) public {
        if (who == address(0)) {
            revert Unauthorized(who);
        }
    }
}
