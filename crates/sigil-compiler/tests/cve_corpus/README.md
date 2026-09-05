# Sigil CVE Retrofit Corpus

10 publicly disclosed CVEs from JS, Solidity, Java, C, Linux, Kubernetes — each classified honestly by scope of claim, with every claim verified mechanically before publication.

**Audit table:** [`/CVE-MATRIX.md`](../../../../CVE-MATRIX.md) — the 60-second skim.

**Sister corpus:** [`/ATTACK-MATRIX.md`](../../../../ATTACK-MATRIX.md) — Sigil's internal 54-attack corpus.

## How this corpus is structured

Each CVE has up to three files in this directory:

- **`<NN>_<cve_id>.sigil`** — vulnerable fixture (only for STRUCTURAL and CLASS scope). When compiled, fires a specific SIGIL diagnostic that demonstrates the language's defense layer rejecting code analogous to the original bug. Includes a `// MUTATION_SITE` line that, when deleted, makes the program compile cleanly — proving the diagnostic pins the specific bug pattern.
- **`<NN>_<cve_id>_safe.sigil`** — safe-form fixture. Demonstrates the idiomatic SIGIL pattern for achieving the original code's legitimate intent (logging, signature verification, file access, etc.). Always present, always `expect-ok`.
- **`<NN>_<cve_id>.md`** — per-CVE writeup. Plain-language explanation of the original bug, the attacker's exploit path, SIGIL's defense mechanism, and citations.

## Three scope-of-claim tiers

| Tier | Meaning | Vulnerable fixture? |
|---|---|---|
| **STRUCTURAL** | SIGIL rejects code that structurally resembles the original CVE's vulnerable shape. The vulnerable fixture is a recognizable port of the original bug. | Yes |
| **CLASS** | SIGIL prevents the broader BUG CLASS the CVE belongs to. The vulnerable fixture is the closest analog rather than a faithful port (the original bug may not directly translate). | Yes |
| **BY-CONSTRUCTION** | SIGIL prevents this CVE by lacking the offending language feature entirely (no `eval()`, no reflection, no shell, etc.). No vulnerable SIGIL fixture exists; the writeup explains why the original bug is structurally inexpressible. | No |

The matrix entry for each CVE lists its tier. Lazy framing that overclaims a STRUCTURAL match is impossible because the driver (`cve_corpus.rs`) cross-validates each row against the actual fixtures.

## Driver enforcement

The harness `cve_corpus.rs` enforces:

1. Each numbered CVE (01..10) has the required files for its tier.
2. Each vulnerable fixture's primary diagnostic matches the matrix's claimed code.
3. Each vulnerable fixture's MUTATION_SITE removal leaves a clean compile.
4. Each safe fixture emits ZERO diagnostics (not just compiles — clean).
5. Each writeup contains the seven required H2 sections with adequate content.
6. Cross-links between the matrix, attack matrix, and writeups are intact.
7. Each writeup includes at least 2 verifiable citations.

## Style guide for adding new CVEs

When adding a new CVE retrofit:

1. **Pick the CVE first, then verify the mapping** (NOT the other way around). Write the vulnerable fixture, compile it, and record the actual diagnostic in `PRE-FLIGHT.md` before writing any other file.
2. **If no diagnostic fires** for an intended STRUCTURAL/CLASS retrofit, reclassify as BY-CONSTRUCTION rather than bending the fixture to fit a desired code.
3. **Safe fixtures demonstrate the legitimate intent**, not "the vulnerable fixture with the bad line removed."
4. **Writeups cite NVD + original disclosure** at minimum.
5. **Mutation site is one line** for STRUCTURAL/CLASS CVEs; the driver removes that line and re-compiles to verify clean compile.
6. **Add the CVE to `CVE-MATRIX.md`** with status and tier matching reality.

## Balance policy

The corpus aims for at least 1 CVE per defense family and no family exceeding 50% of the total. Follow-up PRs should add CVEs with this balance constraint in mind.

Current distribution (after this PR):

| Family | Count |
|---|---|
| Capability / effect / ring | 3 (01 Log4Shell, 05 Citrix, 10 K8s) |
| Linear ownership | 2 (03 DAO, 08 WhatsApp) |
| BY-CONSTRUCTION (language feature absence) | 5 (02 Struts2, 04 Spring4Shell, 06 Shellshock, 07 Drupalgeddon, 09 Jenkins) |

The BY-CONSTRUCTION fraction is high because injection-class bugs (Struts2, Drupalgeddon, Jenkins) and reflection-class bugs (Spring4Shell, Shellshock) all map to "the offending mechanism doesn't exist in SIGIL." This is the honest classification.
