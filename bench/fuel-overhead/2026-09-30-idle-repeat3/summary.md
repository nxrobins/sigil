# Fuel-instrumentation runtime overhead — task098 Levenshtein

Harness `crates/sigil-runtime/examples/fuel_overhead.rs`; profile release; seed 6000845620020262144 (0x5347494c2d443500); lengths [0, 100, 500, 1000]; convergence trailing-30 CV < 5% or 500 samples; 1 warm-up per block discarded; wall time 9 s.

## Workload

- Tool: `task098_levenshtein_distance.sigil` (sha256 `03697a0878001312c0666792c8ebbe65cce40256900061d934c1bbf3d59abbd4`)
- Sanity: `kitten\nsitting` returned `3` on every condition.
- Inputs (two `[a-z]` strings of length L joined by one `\n`; L=0 is the bare `\n`):

| L | input bytes | sha256 | expected output | fuel consumed (A) | budget passed |
|---:|---:|---|---:|---:|---:|
| 0 | 1 | `01ba4719c80b6fe911b091a7c05124b64eeece964e09c058ef8f9805daca546b` | 0 | 8 | 16 |
| 100 | 201 | `138ba85631c07ac11a69014829c9732c5f4eb4b7633bb3d3ff40045e23030192` | 91 | 60714 | 121428 |
| 500 | 1001 | `5f7ecdd7b1c5ac0c1ebaef83fe4880187dcc0f9cb669ddfc453553b66c7d0c77` | 445 | 1503516 | 3007032 |
| 1000 | 2001 | `e51a7408e07ac53c728c9d477c4b9f29d9ff09efee43590e1e6ced3f772f0d1a` | 887 | 6007016 | 12014032 |

## Modules

- A0: 2012 bytes, sha256 `f6fc24c739d58518b22558461644c51588298e693993e62c1ab6f593b47f8e8f`, 5 functions, compiler static fuel budget 264; imports: sigil.fuel_decrement, sigil.send, sigil.ask, sigil.spawn, sigil.alloc, sigil.cap_restrict, sigil.cap_split, sigil.cap_mint.
- A1: 1997 bytes, sha256 `ad693b12487fdb7c3117b923a235a3a788182485db9605db387a21a69baa1d50`; 15 `call 0` sites replaced by `drop` across 5 function bodies; 8 non-code sections copied byte-for-byte (digests equal); validates; zero `call 0` remain.

## Cold first call (shipped path, includes Wasmtime compilation)

| call | condition | µs |
|---:|---|---:|
| 1 | A | 5972.1 |
| 2 | B | 5736.2 |
| 3 | A | 5621.4 |
| 4 | B | 5385.4 |
| 5 | A | 5713.6 |
| 6 | B | 5424.8 |

Mirror `Module::from_binary` alone:

| module | wasmtime fuel | µs |
|---|---|---:|
| A0 | on | 5514.2 |
| A0 | off | 4532.7 |
| A1 | on | 5132.6 |
| A1 | off | 4014.2 |
| A0 | on | 5251.8 |
| A0 | off | 4317.5 |
| A1 | on | 5238.8 |
| A1 | off | 4047.6 |
| A0 | on | 5692.3 |
| A0 | off | 4302.3 |
| A1 | on | 5294.7 |
| A1 | off | 4153.9 |

## Per-block results

| Condition | Module | Path | Fuel | L | n | Warm-up (µs) | Min (µs) | Median (µs) | P90 (µs) | Max (µs) | CV % | Flag | fuel_consumed |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|:-:|---:|
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 0 | 42 | 122.0 | 85.0 | 86.8 | 92.2 | 111.1 | 5.3 | ⚠ | 8 |
| B | A1 | shipped execute_ephemeral | backstop only | 0 | 30 | 138.8 | 85.7 | 87.0 | 89.3 | 96.7 | 2.8 | ✓ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 0 | 30 | 77.0 | 44.2 | 45.3 | 46.9 | 53.3 | 4.2 | ✓ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 0 | 60 | 68.1 | 44.7 | 45.6 | 46.5 | 58.2 | 3.9 | ✓ | 8 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 0 | 63 | 84.4 | 45.4 | 46.6 | 48.6 | 120.6 | 19.9 | ⚠ | 8 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 0 | 57 | 69.6 | 44.8 | 46.4 | 54.4 | 77.9 | 14.3 | ⚠ | 0 |
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 100 | 30 | 6314.6 | 669.7 | 679.1 | 698.2 | 746.5 | 2.7 | ✓ | 60714 |
| B | A1 | shipped execute_ephemeral | backstop only | 100 | 49 | 6135.7 | 315.7 | 324.3 | 362.6 | 373.3 | 5.8 | ⚠ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 100 | 30 | 223.9 | 186.6 | 187.4 | 190.8 | 198.6 | 1.5 | ✓ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 100 | 30 | 580.3 | 557.6 | 564.6 | 569.9 | 632.7 | 2.8 | ✓ | 60714 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 100 | 30 | 651.3 | 629.6 | 637.9 | 646.6 | 666.1 | 1.2 | ✓ | 60714 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 100 | 30 | 324.9 | 273.9 | 275.7 | 283.1 | 289.4 | 1.4 | ✓ | 0 |
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 500 | 30 | 14636.4 | 14560.4 | 14678.8 | 14971.5 | 15675.7 | 1.9 | ✓ | 1503516 |
| B | A1 | shipped execute_ephemeral | backstop only | 500 | 30 | 11272.3 | 5819.4 | 5864.8 | 6252.0 | 6683.8 | 3.6 | ✓ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 500 | 30 | 3618.4 | 3617.6 | 3631.8 | 3678.0 | 3699.4 | 0.7 | ✓ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 500 | 30 | 12800.6 | 12684.5 | 12791.4 | 12871.2 | 13733.1 | 1.7 | ✓ | 1503516 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 500 | 30 | 14649.6 | 14571.2 | 14705.4 | 14813.7 | 14846.8 | 0.5 | ✓ | 1503516 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 500 | 30 | 5836.2 | 5772.0 | 5800.1 | 5890.5 | 6766.6 | 3.3 | ✓ | 0 |
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 1000 | 30 | 64011.8 | 57983.9 | 58255.3 | 60651.1 | 61649.2 | 1.9 | ✓ | 6007016 |
| B | A1 | shipped execute_ephemeral | backstop only | 1000 | 30 | 23146.8 | 23031.1 | 23186.4 | 24586.8 | 24716.8 | 2.8 | ✓ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 1000 | 30 | 14413.0 | 14314.3 | 14373.3 | 14468.6 | 14927.7 | 1.0 | ✓ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 1000 | 30 | 50734.7 | 50659.2 | 50845.0 | 51396.2 | 52599.7 | 0.7 | ✓ | 6007016 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 1000 | 30 | 58439.1 | 58237.9 | 58570.5 | 59223.5 | 60061.7 | 0.7 | ✓ | 6007016 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 1000 | 30 | 23069.7 | 22960.4 | 23074.9 | 23151.8 | 24109.7 | 0.9 | ✓ | 0 |

## Derived on medians, per L (net: each condition minus its own L=0 median)

| L | A (µs) | B (µs) | C (µs) | D (µs) | A/C | B/C | D/C | (A−B)/L² ns | (B−C)/L² ns | (A−B)/fuel ns | A'/A | B'/B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 86.8 | 87.0 | 45.3 | 45.6 | — | — | — | — | — | — | — | — |
| 100 | 679.1 | 324.3 | 187.4 | 564.6 | 4.17 | 1.67 | 3.65 | 35.50 | 9.52 | 5.85 | 0.998 | 0.966 |
| 500 | 14678.8 | 5864.8 | 3631.8 | 12791.4 | 4.07 | 1.61 | 3.55 | 35.26 | 8.77 | 5.86 | 1.005 | 0.996 |
| 1000 | 58255.3 | 23186.4 | 14373.3 | 50845.0 | 4.06 | 1.61 | 3.55 | 35.07 | 8.77 | 5.84 | 1.006 | 0.997 |

## Derived on minima, per L (net: each condition minus its own L=0 minimum)

| L | A (µs) | B (µs) | C (µs) | D (µs) | A/C | B/C | D/C | (A−B)/L² ns | (B−C)/L² ns | (A−B)/fuel ns | A'/A | B'/B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 85.0 | 85.7 | 44.2 | 44.7 | — | — | — | — | — | — | — | — |
| 100 | 669.7 | 315.7 | 186.6 | 557.6 | 4.11 | 1.62 | 3.60 | 35.47 | 8.76 | 5.84 | 0.999 | 0.996 |
| 500 | 14560.4 | 5819.4 | 3617.6 | 12684.5 | 4.05 | 1.60 | 3.54 | 34.97 | 8.64 | 5.81 | 1.003 | 0.999 |
| 1000 | 57983.9 | 23031.1 | 14314.3 | 50659.2 | 4.06 | 1.61 | 3.55 | 34.95 | 8.68 | 5.82 | 1.005 | 0.999 |

## Block order

B:L1000, A':L1000, A':L500, D:L1000, A':L0, C:L1000, B':L0, B:L0, A':L100, A:L100, C:L0, C:L500, B:L500, A:L1000, A:L0, A:L500, B':L100, B':L1000, B':L500, D:L0, B:L100, C:L100, D:L500, D:L100
