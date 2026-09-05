//! SOL-ENUM M-spike: the emitted shape for a Solidity `enum` must be valid SIGIL. The
//! frontend lowers an enum to a `u256` TAG carrier (Solidity enums ARE 0-indexed integers):
//! the enum type → `u256`, `Name.Member` → the member's 0-based index LITERAL, the decl
//! ERASED. This regression pins that shape: a `u256` enum-tag state field, member-index
//! literals, the `0` zero-default (Solidity's enum default = the 0th member), `==` AND an
//! ordered `<` compare on the tag (Solidity enums are ordered), and a member-tag literal as
//! a `u256` map key (the carrier is ready for the deferred enum-as-map-key follow-on).
//! Kept as a permanent regression so a compiler change can't silently invalidate the shape.
//! No caps/solver — compiles in any build.
use sigil_compiler::compile_named_module;

#[test]
fn sol_enum_shape_compiles() {
    let src = r#"module sol_enum_spike;

record C { status: u256, seen: BoundedMap_u256_u256_64 }

impl C {
    pub fn new() -> C {
        return C { status: 0, seen: BoundedMap_u256_u256_64::new() };
    }
    pub fn isPending(self: C) -> bool {
        return (self.status == 0);
    }
    pub fn isClosed(self: C) -> bool {
        return (self.status == 2);
    }
    pub fn below(self: C, s: u256) -> bool {
        return (self.status < s);
    }
    pub fn activate(self: C @Mut) {
        self.status = 1;
    }
    pub fn mark(self: C @Mut) {
        self.seen.insert(1, 1);
    }
}
"#;
    if let Err(e) = compile_named_module("sol_enum_spike.sigil", src.to_string()) {
        let codes: Vec<&str> = e.diagnostics().iter().map(|d| d.code().as_str()).collect();
        let msgs: Vec<&str> = e.diagnostics().iter().map(|d| d.message()).collect();
        panic!("enum-as-u256-tag shape must compile, got {codes:?}\n{msgs:#?}");
    }
}
