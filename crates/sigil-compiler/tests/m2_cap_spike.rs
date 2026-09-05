//! SOL-CAP solver regression: the cap-translated `new()` emission shape (`(C, C_Owner)`
//! tuple return that mints `for` the just-constructed contract, + the `&C_Owner` borrow
//! gate) must compile under the SOLVER (Z3 cap-flow), not just the structural rules. The
//! `sigil-frontends` round-trip tests run no-solver (the CLI is `default-features=false`),
//! so this lives here, where the solver feature is on by default. Pins IMPL-4.
use sigil_compiler::compile_named_module;

#[test]
fn sol_cap_new_shape_compiles_under_solver() {
    let src = "module m2_spike;\n\
cap type C_Deploy { mint_owner }\n\
cap type C_Owner mintable_by C_Deploy { all }\n\
record C { x: u256 }\n\
impl C {\n\
    pub fn new(__fe_deploy: &C_Deploy) -> (C, C_Owner) {\n\
        let c = C { x: 0 };\n\
        return (c, mint C_Owner for c);\n\
    }\n\
    pub fn setX(self: C @Mut, __fe_owner: &C_Owner, v: u256) {\n\
        self.x = v;\n\
    }\n\
}\n";
    if let Err(e) = compile_named_module("m2_spike.sigil", src.to_string()) {
        let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
        panic!("M2 cap new() shape must compile under solver, got {codes:?}");
    }
}
