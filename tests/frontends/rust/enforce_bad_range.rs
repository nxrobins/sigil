// The RS4b enforcement demo: `bad` constructs a `Range { lo: 10, hi: 5 }`, which
// violates the `#[sigil::invariant(lo <= hi)]` — so the trusted compiler's Z3
// refutes the construction. The translator emits the `where` clause faithfully;
// SIGIL is the prover.
#[sigil::invariant(lo <= hi)]
struct Range { lo: i64, hi: i64 }
pub fn bad() -> Range {
    Range { lo: 10, hi: 5 }
}
