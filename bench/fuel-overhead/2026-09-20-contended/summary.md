# Fuel-instrumentation runtime overhead — task098 Levenshtein

> Record of the 2026-09-20 run on a CONTENDED host (resting load 13–25%, other
> cargo builds intermittent; see PERFORMANCE.md's secondary table and its
> host-load caveat). Superseded as the headline by `../2026-09-30-idle/`.
> Note added 2026-09-30: the A'/A and B'/B columns of the two derived tables
> below are RAW ratios — the harness at 2e184a9e printed them under a "net"
> heading; the net values are in PERFORMANCE.md. Nothing else in this file
> was edited after the harness wrote it.

Harness `crates/sigil-runtime/examples/fuel_overhead.rs`; profile release; seed 6000845620020262144; lengths [0, 100, 500, 1000]; convergence trailing-30 CV < 5% or 500 samples; 1 warm-up per block discarded; wall time 79 s.

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
| 1 | A | 3733.3 |
| 2 | B | 3486.9 |
| 3 | A | 3780.1 |
| 4 | B | 3891.8 |
| 5 | A | 3876.5 |
| 6 | B | 3668.3 |

Mirror `Module::from_binary` alone:

| module | wasmtime fuel | µs |
|---|---|---:|
| A0 | on | 3706.9 |
| A0 | off | 3186.2 |
| A1 | on | 3249.3 |
| A1 | off | 2736.2 |
| A0 | on | 3544.3 |
| A0 | off | 3026.6 |
| A1 | on | 3525.8 |
| A1 | off | 2847.4 |
| A0 | on | 3545.2 |
| A0 | off | 2843.7 |
| A1 | on | 3451.2 |
| A1 | off | 2970.5 |

## Per-block results

| Condition | Module | Path | Fuel | L | n | Warm-up (µs) | Min (µs) | Median (µs) | P90 (µs) | Max (µs) | CV % | Flag | fuel_consumed |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|:-:|---:|
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 0 | 35 | 167.4 | 64.7 | 107.3 | 109.9 | 118.2 | 13.2 | ⚠ | 8 |
| B | A1 | shipped execute_ephemeral | backstop only | 0 | 30 | 133.7 | 57.2 | 58.4 | 61.9 | 68.0 | 4.0 | ✓ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 0 | 30 | 97.7 | 31.3 | 32.0 | 32.6 | 38.5 | 4.6 | ✓ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 0 | 31 | 97.3 | 30.3 | 31.3 | 34.0 | 40.0 | 6.0 | ⚠ | 8 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 0 | 30 | 154.1 | 60.3 | 62.0 | 63.5 | 70.1 | 3.6 | ✓ | 8 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 0 | 32 | 153.8 | 59.5 | 61.8 | 69.4 | 74.7 | 6.1 | ⚠ | 0 |
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 100 | 46 | 5566.2 | 421.9 | 429.7 | 841.6 | 868.9 | 34.0 | ✗ | 60714 |
| B | A1 | shipped execute_ephemeral | backstop only | 100 | 84 | 4081.3 | 200.4 | 207.2 | 350.7 | 382.2 | 26.9 | ✗ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 100 | 84 | 274.7 | 118.5 | 121.8 | 180.1 | 193.7 | 19.4 | ⚠ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 100 | 266 | 416.5 | 351.8 | 521.2 | 681.2 | 701.7 | 27.0 | ✗ | 60714 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 100 | 50 | 856.4 | 398.7 | 415.5 | 795.2 | 817.9 | 31.8 | ✗ | 60714 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 100 | 247 | 330.6 | 175.5 | 243.3 | 334.5 | 349.7 | 23.8 | ✗ | 0 |
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 500 | 500 | 11596.4 | 9137.7 | 10785.7 | 14855.6 | 17617.7 | 19.6 | ⚠ | 1503516 |
| B | A1 | shipped execute_ephemeral | backstop only | 500 | 500 | 11676.1 | 3651.1 | 3787.0 | 6737.3 | 7529.7 | 25.0 | ✗ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 500 | 500 | 2334.6 | 2261.1 | 2326.2 | 4045.7 | 4144.9 | 24.9 | ✗ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 500 | 500 | 10544.0 | 7968.5 | 9579.8 | 13461.5 | 16249.5 | 21.0 | ✗ | 1503516 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 500 | 30 | 9235.8 | 9152.4 | 9235.6 | 9295.6 | 9331.5 | 0.5 | ✓ | 1503516 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 500 | 500 | 4796.3 | 3624.0 | 3893.5 | 6546.6 | 7055.1 | 24.3 | ✗ | 0 |
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 1000 | 500 | 41943.0 | 36631.0 | 50736.2 | 62547.1 | 69196.3 | 16.7 | ⚠ | 6007016 |
| B | A1 | shipped execute_ephemeral | backstop only | 1000 | 58 | 14699.2 | 14465.6 | 14532.7 | 14622.5 | 19131.4 | 4.1 | ✓ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 1000 | 500 | 9109.5 | 8992.8 | 9532.4 | 13489.9 | 18951.1 | 17.9 | ⚠ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 1000 | 500 | 31940.3 | 31853.6 | 38696.4 | 46594.9 | 58072.1 | 14.0 | ⚠ | 6007016 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 1000 | 30 | 36604.8 | 36568.0 | 36683.7 | 37097.6 | 37298.4 | 0.6 | ✓ | 6007016 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 1000 | 500 | 18833.5 | 14416.2 | 17988.6 | 22202.5 | 26768.0 | 16.0 | ⚠ | 0 |

## Derived on medians, per L (net: each condition minus its own L=0 median)

| L | A (µs) | B (µs) | C (µs) | D (µs) | A/C | B/C | D/C | (A−B)/L² ns | (B−C)/L² ns | (A−B)/fuel ns | A'/A | B'/B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 107.3 | 58.4 | 32.0 | 31.3 | — | — | — | — | — | — | 0.578 | 1.058 |
| 100 | 429.7 | 207.2 | 121.8 | 521.2 | 3.59 | 1.66 | 5.46 | 17.36 | 5.90 | 2.86 | 0.967 | 1.174 |
| 500 | 10785.7 | 3787.0 | 2326.2 | 9579.8 | 4.65 | 1.63 | 4.16 | 27.80 | 5.74 | 4.62 | 0.856 | 1.028 |
| 1000 | 50736.2 | 14532.7 | 9532.4 | 38696.4 | 5.33 | 1.52 | 4.07 | 36.15 | 4.97 | 6.02 | 0.723 | 1.238 |

## Derived on minima, per L (net: each condition minus its own L=0 minimum)

| L | A (µs) | B (µs) | C (µs) | D (µs) | A/C | B/C | D/C | (A−B)/L² ns | (B−C)/L² ns | (A−B)/fuel ns | A'/A | B'/B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 64.7 | 57.2 | 31.3 | 30.3 | — | — | — | — | — | — | 0.932 | 1.040 |
| 100 | 421.9 | 200.4 | 118.5 | 351.8 | 4.10 | 1.64 | 3.69 | 21.40 | 5.60 | 3.52 | 0.945 | 0.876 |
| 500 | 9137.7 | 3651.1 | 2261.1 | 7968.5 | 4.07 | 1.61 | 3.56 | 21.92 | 5.46 | 3.64 | 1.002 | 0.993 |
| 1000 | 36631.0 | 14465.6 | 8992.8 | 31853.6 | 4.08 | 1.61 | 3.55 | 22.16 | 5.45 | 3.69 | 0.998 | 0.997 |

## Block order

B:L1000, A':L1000, A':L500, D:L1000, A':L0, C:L1000, B':L0, B:L0, A':L100, A:L100, C:L0, C:L500, B:L500, A:L1000, A:L0, A:L500, B':L100, B':L1000, B':L500, D:L0, B:L100, C:L100, D:L500, D:L100
