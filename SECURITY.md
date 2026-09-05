# Security policy

SIGIL's promise is that a program the compiler accepts cannot exceed the capabilities,
taint labels, effects, ownership, and fuel it was granted. A report that shows an accepted
program doing so is the most valuable report this project can receive.

## Reporting

Use GitHub's private vulnerability reporting on this repository: **Security → Report a
vulnerability**. Please do not open a public issue or pull request for a security defect;
a public reproduction of an escape is an exploit for everyone running the toolchain.

A useful report contains the program (or the smallest program that shows the problem), the
rejection you expected, what the compiler or runtime did instead, and the commit or release
you observed it on. A working reproduction under `tests/attack/` conventions is ideal but not
required.

We acknowledge reports within seven days, work on a fix privately, and agree a disclosure
date with the reporter before publishing. Reporters are credited in the fix unless they ask
not to be.

## Scope

- The compiler's security gates: taint, capabilities, rings, effects, ownership, and the
  constant-time discipline — any program they accept that the language's rules say they must
  reject.
- The runtime: capability enforcement, fuel and resource bounds, actor isolation, and the
  FFI shims.
- Certificates: a certificate that verifies for a program that does not satisfy what it
  certifies.
- The foreign front ends: a translated program whose SIGIL form is weaker than the source
  program's declared guarantees.
- The proofs: a Lean statement that does not correspond to the verifier it is claimed to
  describe.

Out of scope: denial of service by a program that is rejected or that exhausts a fuel budget
as designed, findings in third-party dependencies (report those upstream), and issues in
tooling that does not ship in this repository.

## What is already known

Accepted risks are recorded, with owners and review points, in
[`docs/RESIDUAL_RISKS.md`](docs/RESIDUAL_RISKS.md); the claims the test suite enforces, and
the counted list of claims it does not yet enforce, are in
[`docs/CLAIMS.md`](docs/CLAIMS.md); known attack-surface gaps are in
[`tests/attack/KNOWN_GAPS.md`](tests/attack/KNOWN_GAPS.md). A report against a listed
accepted risk is still welcome when it comes with a concrete exploit: an accepted risk is a
judgement about likelihood, and a working exploit changes it.

## Supported versions

The `main` branch and the latest tagged release. Fixes land on `main` first.
