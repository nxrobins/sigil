# CVE Retrofit Corpus — Pre-Execution Gate Output

This document records the actual diagnostic each vulnerable fixture emits during the pre-execution gate. The CVE matrix (`/CVE-MATRIX.md`) is written FROM this table, not from assumed mappings.

The driver test `cve_corpus.rs::matrix_codes_match_fixtures` cross-validates each row in `CVE-MATRIX.md` against what each fixture actually emits, so a future fixture change that shifts the primary diagnostic without updating the matrix fails the test.

## Captured diagnostics (default features; no solver)

| # | Fixture | Tier | Primary diagnostic emitted | Notes |
|---|---|---|---|---|
| 01 | `01_cve_2021_44228_log4shell.sigil` | STRUCTURAL | **E003** | Inner-ring function declaring `FFI, Unsafe` |
| 02 | (no vulnerable fixture) | BY-CONSTRUCTION | — | No `eval()` in SIGIL — see writeup |
| 03 | `03_dao_reentrancy.sigil` | CLASS | **O001** | Use-after-move on linear cap into second `send` |
| 04 | (no vulnerable fixture) | BY-CONSTRUCTION | — | No reflection in SIGIL — see writeup |
| 05 | `05_cve_2019_19781_citrix.sigil` | STRUCTURAL | **E003** | Inner-ring function declaring `FFI, Unsafe` |
| 06 | (no vulnerable fixture) | BY-CONSTRUCTION | — | No shell in SIGIL — see writeup |
| 07 | (no vulnerable fixture) | BY-CONSTRUCTION | — | No string-to-SQL in SIGIL — see writeup |
| 08 | `08_cve_2019_11932_whatsapp.sigil` | CLASS | **O001** | Use-after-move on linear cap into second `send` |
| 09 | (no vulnerable fixture) | BY-CONSTRUCTION | — | No polymorphic deserializer in SIGIL — see writeup |
| 10 | `10_cve_2018_1002105_k8s.sigil` | STRUCTURAL | **T096** | Spawn-init arg must be cap-typed (passed `i64`) |

## Tier balance

| Tier | Count | CVEs |
|---|---|---|
| STRUCTURAL | 3 | 01, 05, 10 |
| CLASS | 2 | 03, 08 |
| BY-CONSTRUCTION | 5 | 02, 04, 06, 07, 09 |
| **Total** | **10** | |

## Notes on classification

- During the pre-execution gate, two CVEs initially tagged STRUCTURAL/CLASS reclassified after the fixture failed to fire the assumed diagnostic. The taint lattice (`Public < Internal < Secret`) catches information leakage, not injection — so injection-class CVEs (Struts2, Drupalgeddon) that I'd hoped to retrofit as STRUCTURAL with T001 are actually BY-CONSTRUCTION: SIGIL has no `eval()` or string-as-code mechanism for injection to land on.
- The K8s fixture emits T095 + T096 — both are init-arg type-checks. The matrix lists T096 as the primary (it's the load-bearing rule: "spawn init arguments must be capability-typed").
- The Citrix and Log4Shell fixtures both emit E003 (inner-ring function declares privilege effects). This is the same SIGIL primitive applied to two different real-world bugs; the writeups distinguish the bug shapes.

## How to regenerate this table

```powershell
for f in crates/sigil-compiler/tests/cve_corpus/*.sigil; do
  if [[ "$f" != *_safe.sigil ]]; then
    echo "=== $f ==="
    cargo run -p sigil --quiet -- check --json "$f" 2>&1 | grep -E '"code"' | head -1
  fi
done
```

The driver runs this same check on every test invocation and asserts agreement with the matrix.
