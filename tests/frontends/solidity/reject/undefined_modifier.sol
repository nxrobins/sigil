// expect-fe: FE451
// A function applies a modifier with no matching declaration — never silently drop the
// guard (a typo'd `onlyOwner` must reject, not run unguarded).
pragma solidity ^0.8.0;
contract C {
    uint256 x;

    function setX(uint256 v) public onlyOwner {
        x = v;
    }
}
