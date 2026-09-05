//! SOL-STRUCT M-spike: the emitted shape for a struct-using Solidity contract must be
//! valid SIGIL. A user `struct`→`record` plus the contract record holding it (a
//! record-in-record state field), with a nested zero-init in `new()`, field read/write,
//! whole-struct construction, and a struct param + struct return. Record-in-record and
//! nested record literals are core SIGIL, so this is low-risk insurance (vs. SOL-CAP /
//! SOL-ERC20's genuinely-novel shapes) — but it confirms the exact emit shape before M2
//! builds on it. Kept as a permanent regression. No caps/solver — compiles in any build.
use sigil_compiler::compile_named_module;

#[test]
fn sol_struct_shape_compiles() {
    let src = r#"module sol_struct_spike;

record Point { x: u256, y: u256 }

record C { p: Point, n: u256 }

impl C {
    pub fn new() -> C {
        return C { p: Point { x: 0, y: 0 }, n: 0 };
    }
    pub fn getX(self: C) -> u256 {
        return self.p.x;
    }
    pub fn setX(self: C @Mut, v: u256) {
        self.p.x = v;
    }
    pub fn setP(self: C @Mut, a: u256, b: u256) {
        self.p = Point { x: a, y: b };
    }
    pub fn mkPoint(a: u256, b: u256) -> Point {
        return Point { x: a, y: b };
    }
    pub fn sumPoint(pt: Point) -> u256 {
        return pt.x + pt.y;
    }
}
"#;
    if let Err(e) = compile_named_module("sol_struct_spike.sigil", src.to_string()) {
        let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
        let msgs: Vec<&str> = e.diagnostics().iter().map(|d| d.message()).collect();
        panic!("struct-in-record shape must compile, got {codes:?}\n{msgs:#?}");
    }
}
