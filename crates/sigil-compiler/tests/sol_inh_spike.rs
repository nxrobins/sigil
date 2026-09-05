//! SOL-INH M-spike: the two NOVEL shapes that inheritance flattening will emit must be valid
//! SIGIL. Flatten merges a base+derived hierarchy into ONE flat `Contract` the existing
//! pipeline then lowers; the merged OUTPUT is an ordinary flat contract, so the only genuinely
//! new shapes are (1) an inherited modifier inlined into the derived function that applies it
//! (the headline existential — the guard must survive the merge) and (2) the hygienic
//! base-constructor ARG binding (alpha-renamed `__fe_ctor<i>_<param>` locals + a let-prelude,
//! NOT textual substitution). This pins both as permanent regressions: a trusted-compiler
//! change can't silently invalidate the merge target. No caps/solver — compiles in any build.
use sigil_compiler::compile_named_module;

fn must_compile(name: &str, src: &str) {
    if let Err(e) = compile_named_module(name.to_string(), src.to_string()) {
        let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
        let msgs: Vec<&str> = e.diagnostics().iter().map(|d| d.message()).collect();
        panic!("SOL-INH merge target must compile, got {codes:?}\n{msgs:#?}");
    }
}

/// `contract A { address owner; modifier onlyOwner(){ require(msg.sender==owner); _; } }`
/// `contract B is A { uint256 value; function setValue(uint256 v) public onlyOwner { value=v; } }`
/// flattens to one `B` whose `setValue` has the INHERITED `onlyOwner` guard inlined (EX-3:
/// the guard from the base modifier must appear in the merged output).
#[test]
fn sol_inh_inherited_guard_shape_compiles() {
    let src = r#"module sol_inh_guard;

record B { owner: u256, value: u256 }

impl B {
    pub fn new() -> B {
        return B { owner: 0, value: 0 };
    }
    pub fn setValue(self: B @Mut, __fe_sender: u256, v: u256) {
        trap_if(!((__fe_sender == self.owner)));
        self.value = v;
    }
}
"#;
    must_compile("sol_inh_guard.sigil", src);
}

/// `contract Base { uint256 v; constructor(uint256 x){ v = x; } }`
/// `contract Tok is Base { constructor() Base(7) {} }`
/// flattens to one `Tok` whose synthesized `new()` chains Base's ctor body with `x` bound to
/// the supplied `7` via a fresh `__fe_ctor0_x` local + a let-prelude (EX-6: hygienic
/// alpha-rename, type-annotated from the base param, never textual substitution).
#[test]
fn sol_inh_ctor_arg_binding_shape_compiles() {
    let src = r#"module sol_inh_ctor;

record Tok { v: u256 }

impl Tok {
    pub fn new() -> Tok {
        let mut __fe_c = Tok { v: 0 };
        let __fe_ctor0_x: u256 = 7;
        __fe_c.v = __fe_ctor0_x;
        return __fe_c;
    }
}
"#;
    must_compile("sol_inh_ctor.sigil", src);
}
