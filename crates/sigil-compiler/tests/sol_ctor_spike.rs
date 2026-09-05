//! SOL-CTOR M-spike: the emitted shape for a Solidity `constructor(params){body}` must be
//! valid SIGIL. The frontend lowers it to a `new(params) -> C` that BUILDS the record
//! (`let mut __fe_c = C { …zero-defaults… }`), RUNS the body (field writes + a guard) on the
//! local, and RETURNS it. Two properties this regression pins: (1) build-mutate-return —
//! `let mut __fe_c` + field assigns + `trap_if` + `return __fe_c`; and (2) CEI-exempt locals
//! (EX-2) — the write → checked-arith → trap → write ordering that is a hard FE412 against a
//! `self.field` storage write is FINE on `__fe_c` (a local record not yet returned/deployed,
//! so a trap just unwinds `new()`, faithful to a Solidity revert-on-deploy; nothing persists).
//! Kept as a permanent regression so a compiler change can't silently invalidate the shape
//! the frontend emits. No caps/solver — compiles in any build.
use sigil_compiler::compile_named_module;

#[test]
fn sol_ctor_shape_compiles() {
    let src = r#"module sol_ctor_spike;

record C { owner: u256, total: u256 }

impl C {
    pub fn new(initial: u256, __fe_sender: u256) -> C {
        let mut __fe_c = C { owner: 0, total: 0 };
        __fe_c.owner = __fe_sender;
        __fe_c.total = initial;
        trap_if(initial == 0);
        return __fe_c;
    }

    pub fn mk(a: u256, b: u256) -> C {
        let mut __fe_c = C { owner: 0, total: 0 };
        __fe_c.owner = a;
        let s = (a + b);
        trap_if(s == 0);
        __fe_c.total = s;
        return __fe_c;
    }
}
"#;
    if let Err(e) = compile_named_module("sol_ctor_spike.sigil", src.to_string()) {
        let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
        let msgs: Vec<&str> = e.diagnostics().iter().map(|d| d.message()).collect();
        panic!("constructor build-mutate-return shape must compile, got {codes:?}\n{msgs:#?}");
    }
}
