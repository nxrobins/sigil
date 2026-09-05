// expect-fe: FE472
// A state var shadowed across the hierarchy — `x` in both A and B. solc bans this post-0.6; flatten
// rejects it so no merge can mis-layout / mis-resolve which field a read or write targets.
pragma solidity ^0.8.0;
contract A { uint256 x; }
contract B is A { uint256 x; }
