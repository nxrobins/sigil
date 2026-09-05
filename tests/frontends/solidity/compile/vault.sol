// SOL0 demo: a scalar-balance vault. The classic underflow drain bug
// (`balance -= amount` wrapping to a huge number) is impossible in the emitted
// SIGIL — `u256` subtraction is checked and traps — and `require` is a faithful
// runtime guard. Checks-then-effects: the guard precedes the single state write.
pragma solidity ^0.8.0;

contract Vault {
    uint256 balance;

    function withdraw(uint256 amount) public {
        require(balance >= amount);
        balance -= amount;
    }
}
