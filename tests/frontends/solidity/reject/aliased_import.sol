// expect-fe: FE476
// An aliased import renames a symbol flatten can't silently drop — fail closed.
pragma solidity ^0.8.0;
import {ERC20 as Token} from "./ERC20.sol";
contract C { uint256 x; }
