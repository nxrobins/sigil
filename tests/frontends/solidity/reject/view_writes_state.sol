// expect-fe: FE446
// SOL1b adversarial-review fix (OBS-1): a `view`/`pure` function that writes state is
// invalid Solidity; the frontend now rejects it early with a precise code rather than
// emitting a non-@Mut method that only the trusted compiler's @ReadOnly check catches.
pragma solidity ^0.8.0;
contract C {
    mapping(address => uint256) bal;
    function f(address to, uint256 a) public view {
        bal[msg.sender] -= a;
        bal[to] += a;
    }
}
