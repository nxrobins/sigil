# Neutral package-boundary fixture

This test-only graph is not a library candidate. `test/app` depends on
`test/helper` and exists only to exercise the local package protocol.

- `Public` round-trip: public input and result remain public across a package boundary.
- `Internal` round-trip: internal input and result remain internal across that boundary.
- `Secret` round-trip: secret input and result remain secret across that boundary.
- Both packages are inner-ring and effect-free; their manifests claim exactly that derived surface.
- The checked-in lock is dependency-first and binds exact manifest, content, stdlib, and graph hashes.

Tests copy this tree before applying negative mutations. Mutated trees are ephemeral and never
become canonical package views.

The focused test targets name each additional obligation:

- `repeated_package_builds_are_byte_identical`: graph order/hash, normalized source framing,
  lock-verification result, Wasm, and certificate bytes are stable across repeated builds.
- `internal_result...` / `secret_result...`: confidentiality cannot weaken into Public at a package
  call boundary (`T001`).
- `inner_package_cannot_call...trusted_outer`: a manifest cannot represent outer/trusted code as
  inner and an inner caller cannot cross the ring (`R004`).
- `compiler_derived_*_override_manifest_understatement`: effects, imports, grants, and taint facts
  come from the compiler, not manifest authority.
- missing/offline, feature, version/source, cycle, yank, order, hash, and both collision tests prove
  the named resolver/security failures.
- strict-shape, tampered-field, and replay tests prove graph certificates fail closed.
