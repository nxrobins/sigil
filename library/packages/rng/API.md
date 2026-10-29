# Seeded RNG contract

Private `sigil/rng` version `0.1.0-public.1`; inner ring, Public-only,
state-relative, no host imports or grants. Algorithm identity is
`pcg-xsh-rr-64-32-v1`. All constructors allocate; all other APIs allocate no
memory. Live constructor-owned records are required; record fields are not
sealed against callers. This is not cryptographic randomness.

## Initialization and draws

`new(seed:u64,stream:u64)->SeedRng` accepts all 64 seed bits and stream IDs
0..2^63-1. A larger stream returns a record with `error=-400`; check it before
use. Seeding matches PCG's two-step initialization: odd increment 2*stream+1,
zero state advanced once, seed added, then advanced again. State transitions
wrap modulo 2^64 using multiplier 6364136223846793005. Output is XSH-RR: xor
with right-shift 18, right-shift 27, truncate to 32 bits, rotate right by the
old state's top five bits. All output bits fit in a nonnegative i64.

`next(rng @Mut)->i64` returns 0..2^32-1 and advances once; invalid generator
metadata returns -400 without changing it.

`below(rng @Mut,bound:i64)->i64` accepts bounds 1..2^32 and returns [0,bound).
Reject raw draws below 2^32 modulo bound before taking a remainder. Unlike the
unbounded reference loop, at most 32 raw draws are tried. Exhaustion returns
-429 and preserves the original state. Invalid bounds or generator metadata
return -400 without changing state. The successful rejection mapping removes
modulo bias; it is not a claim of independent or cryptographically random draws.

`new_int()->RngInt` allocates an integer output cell. `signed_into(rng @Mut,
radius:i64,out @Mut)->i64` writes a value in [-radius,radius], for radius
0..2^31-1, using `below(2*radius+1)`. It returns 0 on success; invalid input
returns -400, exhaustion -429. Both generator and output are unchanged on
returned errors. Negative samples are data in the cell, not status codes.

`new_float()->RngFloat` allocates a float output cell. `unit_into(rng @Mut,
out @Mut)->i64` writes `next()/2^32`, exactly representable in f64, from the
discrete grid [0,1) with spacing 2^-32. It uses one draw and a fixed 32-bit
conversion loop. On -400, generator and output remain unchanged.

## Save and restore

`new_snapshot()->RngSnapshot` allocates a snapshot. `snapshot_into(rng @ReadOnly,
out @Mut)->i64` writes version=1, the current u64 state and the odd u64
increment. Invalid generator metadata returns -400 and preserves the snapshot.

`restore(rng @Mut,snapshot @ReadOnly)->i64` validates version=1 and odd
increment, then replaces the generator state and clears its constructor error.
Invalid snapshots return -400 and preserve the generator. This explicit reset
may initialize a failed constructor result. Even increments and unknown
versions are refused, not normalized. Snapshot fields identify this algorithm
only; a surrounding checkpoint must also bind the application's own version.

The canonical snapshot payload is three little-endian 64-bit words: version
(i64), value (u64), increment (u64). JSON transports must preserve both unsigned
integers exactly, rather than passing them through a binary64 number type.

## Boundaries

The same state and calls reproduce the same sequence on conforming implementations.
This deliberately changes autoresearch's earlier 31-bit LCG stream and its
15-bit modulo sampler; no old-seed trajectory equivalence is claimed.
Operations are transactional only on returned errors. Fuel exhaustion or
traps can interrupt execution; persistent callers publish a new checkpoint
only after a complete successful request. Secret/Internal inputs require a
separate label-aware API; this package must not launder them to Public.
