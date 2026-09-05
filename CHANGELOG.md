# Changelog

User-visible **language-semantics** changes — the entries that change what an existing
program *means* or whether it still compiles. Checker strengthenings, internal refactors,
and tooling live in PR history and `docs/CLAIMS.md`; they do not repeat here.

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
