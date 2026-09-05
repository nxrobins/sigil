// SOL-XFILE PR2/L2: an INTERFACE used as an inheritance base is now ADMITTED — its body is
// parse-skipped (bodiless signatures contribute nothing to a flattened concrete, and solc
// already verified conformance), so `contract B is I` flattens to just B's own members. (An
// ABSTRACT base, by contrast, contributes its parsed members; a LIBRARY base stays FE476.)
pragma solidity ^0.8.0;
interface I { function f() external; }
contract B is I { uint256 y; }
