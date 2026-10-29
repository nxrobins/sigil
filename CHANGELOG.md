# Changelog

User-visible **language-semantics** changes — the entries that change what an existing
program *means* or whether it still compiles. Checker strengthenings, internal refactors,
and tooling live in PR history and `docs/CLAIMS.md`; they do not repeat here.

## 2026-10 — `ct_lt` orders every 8-byte pair

`ct_lt(a, b)` now gives the true order on all 64 bits: signed for two `i64`, unsigned for two
`u64`. It used to return the sign bit of the wrapping `a - b`, which was wrong whenever the true
difference did not fit in an `i64` (`ct_lt(i64::MIN, 1)` was false, `ct_lt(i64::MAX, -1)` was
true), and it read a `u64` as signed (a `u64` of 2^63 or more ordered below 0). A program that
compared such a pair now gets the other answer.

- **Mixed signedness is rejected.** One `i64` and one `u64` operand have no single order, so
  `ct_lt` on that pair is **T075**, as `<` rejects the same pair. Convert one operand with
  `.as_i64()` or `.as_u64()`: the conversion keeps all 64 bits and picks the order.
- **A literal beside a `u64` is a `u64`.** So a negative literal there, as in `ct_lt(-1, x)`, is
  now **T075**; it used to compile and compare signed.
- **An `i32` widened with `.as_u64()`** is a `u64`, so `ct_lt` now compares it unsigned: a
  negative one orders above every non-negative one, where it used to keep the `i32` order. Widen
  an `i32` with `.as_i64()` to keep it; the **T075** hint for a 4-byte operand now says so.
- **Constant time.** Each order is a fixed sequence of ALU operations on the operands and a
  constant shift, with no branch, `select` or division (`taint_ct_audit.rs` scans both).
- **Unchanged.** `ct_eq` and `ct_select`. A pair of two `i64` whose true difference fits in an
  `i64` keeps its answer, and so does a pair of two `u64` below 2^63; every 4-byte pair widened
  as the **T075** hint advises is one of these.

## 2026-08 — `str ==` compares bytes (PR #699)

`str` `==` / `!=` and `match` on a string literal now compare **content**: length first,
then a byte scan (`AirStmt::StrBytesEq`). Previously they compared `data_ptr` alone —
not even identity, since `len` was ignored: two byte-equal strings built at different
sites compared unequal, a `match` on a constructed scrutinee missed its literal arm, and
`s.substr(0, k) == s` was *true* for every `k` (a view shares its parent's start
address). All three were silent wrong answers; all three now answer by bytes.

- **Cost.** `==` on `str` is O(len) and burns fuel proportional to the compared length
  (one decrement up front, one per loop iteration). A function containing one is no
  longer a static workload ceiling — its worst case depends on runtime string lengths
  (`fuel_is_workload_ceiling` reports `false`).
- **Security.** `==` / `!=` where either `str` operand is `@SecretCT` is rejected at
  compile time (**T033** / CT018): the early-exit byte scan is a timing channel. Fold a
  constant-time compare over `byte_at`, accept the length leak explicitly with
  `bytes_eq`, or `declassify_ct` first.
- **Unchanged.** `str.bytes_eq` keeps its behavior and is now equivalent to `==`. The
  certified self-host source uses `bytes_eq` throughout and is fenced to zero `str ==`
  uses, so the committed seed's bytes did not move.
