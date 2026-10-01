# Fuel-instrumentation runtime overhead — task098 Levenshtein

Harness `crates/sigil-runtime/examples/fuel_overhead.rs`; profile release; seed 6000845620020262144 (0x5347494c2d443500); lengths [0, 100, 500, 1000]; convergence trailing-30 CV < 5% or 500 samples; 1 warm-up per block discarded; wall time 10 s.

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
| 1 | A | 6035.5 |
| 2 | B | 5751.2 |
| 3 | A | 5871.2 |
| 4 | B | 5413.2 |
| 5 | A | 5779.5 |
| 6 | B | 5480.0 |

Mirror `Module::from_binary` alone:

| module | wasmtime fuel | µs |
|---|---|---:|
| A0 | on | 5574.7 |
| A0 | off | 4553.1 |
| A1 | on | 5079.4 |
| A1 | off | 4150.2 |
| A0 | on | 5350.9 |
| A0 | off | 4295.4 |
| A1 | on | 5058.5 |
| A1 | off | 4086.6 |
| A0 | on | 5384.5 |
| A0 | off | 4349.4 |
| A1 | on | 5100.5 |
| A1 | off | 4098.9 |

## Per-block results

| Condition | Module | Path | Fuel | L | n | Warm-up (µs) | Min (µs) | Median (µs) | P90 (µs) | Max (µs) | CV % | Flag | fuel_consumed |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|:-:|---:|
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 0 | 30 | 123.0 | 81.8 | 83.0 | 85.1 | 97.3 | 4.0 | ✓ | 8 |
| B | A1 | shipped execute_ephemeral | backstop only | 0 | 30 | 134.3 | 82.2 | 83.4 | 86.8 | 91.2 | 2.8 | ✓ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 0 | 30 | 73.5 | 41.9 | 42.8 | 44.0 | 47.6 | 2.5 | ✓ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 0 | 30 | 62.2 | 42.1 | 43.0 | 43.8 | 46.9 | 2.0 | ✓ | 8 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 0 | 30 | 81.5 | 42.7 | 43.4 | 44.3 | 49.0 | 2.6 | ✓ | 8 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 0 | 30 | 67.6 | 42.3 | 43.1 | 44.3 | 53.0 | 4.7 | ✓ | 0 |
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 100 | 30 | 6704.8 | 665.2 | 671.4 | 681.2 | 774.4 | 3.6 | ✓ | 60714 |
| B | A1 | shipped execute_ephemeral | backstop only | 100 | 30 | 5983.4 | 311.7 | 313.1 | 324.8 | 375.7 | 4.0 | ✓ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 100 | 30 | 220.1 | 183.0 | 184.1 | 193.2 | 215.8 | 3.5 | ✓ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 100 | 30 | 579.1 | 554.2 | 563.5 | 578.9 | 638.8 | 3.1 | ✓ | 60714 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 100 | 30 | 729.6 | 701.7 | 708.6 | 714.7 | 750.2 | 1.2 | ✓ | 60714 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 100 | 30 | 325.5 | 270.9 | 273.3 | 281.4 | 318.4 | 3.2 | ✓ | 0 |
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 500 | 30 | 14779.6 | 14562.6 | 14655.1 | 16519.6 | 16705.4 | 4.9 | ✓ | 1503516 |
| B | A1 | shipped execute_ephemeral | backstop only | 500 | 30 | 11504.9 | 5812.6 | 5849.1 | 5884.1 | 5982.6 | 0.7 | ✓ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 500 | 30 | 3632.1 | 3616.0 | 3623.8 | 3701.7 | 3767.8 | 1.0 | ✓ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 500 | 30 | 12874.0 | 12682.6 | 12793.5 | 13027.2 | 13582.1 | 1.5 | ✓ | 1503516 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 500 | 30 | 17281.2 | 17068.7 | 17219.0 | 17756.4 | 18660.4 | 2.0 | ✓ | 1503516 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 500 | 30 | 5807.1 | 5769.9 | 5789.9 | 5864.1 | 5922.7 | 0.7 | ✓ | 0 |
| A | A0 | shipped execute_ephemeral | host decrements + backstop | 1000 | 30 | 63847.1 | 58017.7 | 58399.6 | 65815.6 | 66674.3 | 4.9 | ✓ | 6007016 |
| B | A1 | shipped execute_ephemeral | backstop only | 1000 | 30 | 23295.4 | 23025.6 | 23100.9 | 23271.0 | 23396.8 | 0.4 | ✓ | 0 |
| C | A1 | mirror, wasmtime fuel off | none | 1000 | 30 | 14333.6 | 14315.0 | 14387.2 | 14735.9 | 15022.5 | 1.3 | ✓ | 0 |
| D | A0 | mirror, wasmtime fuel off | host decrements only | 1000 | 30 | 51844.3 | 50987.3 | 51262.5 | 51387.3 | 51912.4 | 0.4 | ✓ | 6007016 |
| A' | A0 | mirror, wasmtime fuel on | host decrements + backstop | 1000 | 30 | 68507.7 | 68275.5 | 68586.0 | 69241.6 | 70863.2 | 0.7 | ✓ | 6007016 |
| B' | A1 | mirror, wasmtime fuel on | backstop only | 1000 | 30 | 23808.0 | 22964.3 | 23044.6 | 23234.1 | 23623.6 | 0.7 | ✓ | 0 |

## Derived on medians, per L (net: each condition minus its own L=0 median)

| L | A (µs) | B (µs) | C (µs) | D (µs) | A/C | B/C | D/C | (A−B)/L² ns | (B−C)/L² ns | (A−B)/fuel ns | A'/A | B'/B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 83.0 | 83.4 | 42.8 | 43.0 | — | — | — | — | — | — | — | — |
| 100 | 671.4 | 313.1 | 184.1 | 563.5 | 4.16 | 1.63 | 3.68 | 35.87 | 8.84 | 5.91 | 1.131 | 1.002 |
| 500 | 14655.1 | 5849.1 | 3623.8 | 12793.5 | 4.07 | 1.61 | 3.56 | 35.23 | 8.74 | 5.86 | 1.179 | 0.997 |
| 1000 | 58399.6 | 23100.9 | 14387.2 | 51262.5 | 4.07 | 1.60 | 3.57 | 35.30 | 8.67 | 5.88 | 1.175 | 0.999 |

## Derived on minima, per L (net: each condition minus its own L=0 minimum)

| L | A (µs) | B (µs) | C (µs) | D (µs) | A/C | B/C | D/C | (A−B)/L² ns | (B−C)/L² ns | (A−B)/fuel ns | A'/A | B'/B |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 81.8 | 82.2 | 41.9 | 42.1 | — | — | — | — | — | — | — | — |
| 100 | 665.2 | 311.7 | 183.0 | 554.2 | 4.13 | 1.63 | 3.63 | 35.39 | 8.84 | 5.83 | 1.130 | 0.996 |
| 500 | 14562.6 | 5812.6 | 3616.0 | 12682.6 | 4.05 | 1.60 | 3.54 | 35.00 | 8.63 | 5.82 | 1.176 | 1.000 |
| 1000 | 58017.7 | 23025.6 | 14315.0 | 50987.3 | 4.06 | 1.61 | 3.57 | 34.99 | 8.67 | 5.83 | 1.178 | 0.999 |

## Block order

B:L1000, A':L1000, A':L500, D:L1000, A':L0, C:L1000, B':L0, B:L0, A':L100, A:L100, C:L0, C:L500, B:L500, A:L1000, A:L0, A:L500, B':L100, B':L1000, B':L500, D:L0, B:L100, C:L100, D:L500, D:L100
