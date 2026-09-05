//! The single gate through which every bump/arena allocation size must pass.
//!
//! SIGIL has two hosts with two DIFFERENT heap models — the forge's single bump pointer
//! (`ephemeral::alloc_from_bump`) and the actor runtime's per-actor 64 KB arenas
//! (`runtime::alloc_import`). They cannot share an *allocator*. But they share one *contract*:
//! a byte count handed to an allocator must be a legitimate non-negative size. That contract
//! was enforced ad hoc — the forge sign-checked its guest `i32`, the actor did not, and the
//! actor's subsequent `(size + 7)` overflowed u32 and PANICKED the host on a negative input
//! (runtime.rs, pre-fix). The current contract is in
//! docs/specs/runtime-differential-census.md.
//!
//! [`AllocBytes`] makes the contract enforceable at the TYPE level: its inner `u32` is private,
//! so the only ways to obtain one are the two named constructors below. An allocator that takes
//! an `AllocBytes` therefore CANNOT be reached with an unvalidated size, and a future third
//! allocator cannot skip the gate without changing this file. Compile-time prevention, not a
//! runtime hope.
//!
//! There are exactly two provenances, and they are NAMED (greppable, like `expect`), never
//! silent:
//! - [`AllocBytes::checked_from_guest`] — a guest-controlled `i32`; a negative value is rejected.
//!   This is the boundary that drifted and crashed.
//! - [`AllocBytes::from_host_len`] — a host-controlled `u32` length the host already vouches is a
//!   legitimate size (e.g. `input.len()` after the memory-budget check). No sign question exists.

/// A byte count that has been proven a legitimate non-negative allocation size. Constructable
/// only via the two named constructors; the inner value is private so no other path can mint one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AllocBytes(u32);

/// Why a guest allocation size was rejected. Carries the offending `i32` for the diagnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocSizeError {
    /// The guest passed a negative size — never a legal allocation.
    Negative(i32),
}

impl core::fmt::Display for AllocSizeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AllocSizeError::Negative(n) => {
                write!(f, "alloc size must be non-negative, found `{n}`")
            }
        }
    }
}

impl AllocBytes {
    /// The GUEST boundary: a non-negative `i32` becomes an `AllocBytes`, a negative one is
    /// rejected. This is the single point at which the guest-size contract is enforced for BOTH
    /// hosts — the whole point of the type.
    pub fn checked_from_guest(size: i32) -> Result<Self, AllocSizeError> {
        u32::try_from(size)
            .map(AllocBytes)
            .map_err(|_| AllocSizeError::Negative(size))
    }

    /// A HOST-controlled length the caller vouches is a legitimate size (already non-negative by
    /// construction — a Rust `usize`/`u32` length, not a guest `i32`). Named so the vouch is
    /// auditable, never an accidental bypass of the guest check.
    pub fn from_host_len(len: u32) -> Self {
        AllocBytes(len)
    }

    /// The validated byte count. A `checked_from_guest` value is guaranteed `<= i32::MAX as u32`
    /// (2^31 - 1), so `+ 7` for an 8-alignment cannot overflow — the property that removes the
    /// actor's panic edge.
    pub fn get(self) -> u32 {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use super::{AllocBytes, AllocSizeError};

    #[test]
    fn guest_accepts_non_negative() {
        assert_eq!(AllocBytes::checked_from_guest(0).unwrap().get(), 0);
        assert_eq!(AllocBytes::checked_from_guest(16).unwrap().get(), 16);
        assert_eq!(
            AllocBytes::checked_from_guest(i32::MAX).unwrap().get(),
            i32::MAX as u32
        );
    }

    #[test]
    fn guest_rejects_negative() {
        assert_eq!(
            AllocBytes::checked_from_guest(-1),
            Err(AllocSizeError::Negative(-1))
        );
        assert_eq!(
            AllocBytes::checked_from_guest(i32::MIN),
            Err(AllocSizeError::Negative(i32::MIN))
        );
    }

    #[test]
    fn a_guest_validated_size_cannot_overflow_the_align_up() {
        // The invariant that removes the panic: a guest-validated size + 7 stays within u32.
        let max = AllocBytes::checked_from_guest(i32::MAX).unwrap().get();
        assert!(max.checked_add(7).is_some());
    }

    #[test]
    fn host_len_passes_through() {
        assert_eq!(AllocBytes::from_host_len(4096).get(), 4096);
    }
}
