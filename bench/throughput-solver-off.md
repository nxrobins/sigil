# Compile throughput — solver=OFF

Convergence: per-fixture sample count is bounded above by 500, minimum 30, terminates when trailing CV < 5.0%.
Fixtures with CV ≥ 20% are dropped from per-corpus medians/totals (✗ flag).

## Per-corpus summary (solver=OFF)

| Corpus | Files measured | Dropped (CV>20%) | Median (μs) | P90 (μs) | Total (μs) |
|---|---:|---:|---:|---:|---:|
| fixtures | 11 | 19 | 6 | 13 | 66 |
| cve_corpus | 9 | 6 | 26 | 29 | 220 |
| z3_corpus | 12 | 12 | 28 | 45 | 341 |

## fixtures — per-fixture detail (solver=OFF)

| Fixture | n | Median (μs) | P90 (μs) | Max (μs) | CV % | Flag |
|---|---:|---:|---:|---:|---:|:-:|
| E003.sigil | 319 | 10 | 14 | 35 | 27.4 | ✗ |
| N007.sigil | 35 | 4 | 5 | 6 | 10.9 | ⚠ |
| N008.sigil | 64 | 16 | 18 | 26 | 14.6 | ⚠ |
| N009.sigil | 30 | 5 | 5 | 6 | 3.6 | ✓ |
| N011.sigil | 30 | 1 | 1 | 1 | 0.0 | ✓ |
| R003.sigil | 500 | 9 | 13 | 30 | 35.1 | ✗ |
| R004.sigil | 255 | 25 | 30 | 92 | 29.3 | ✗ |
| R006.sigil | 500 | 8 | 10 | 32 | 26.6 | ✗ |
| S004.sigil | 31 | 0 | 0 | 1 | 556.8 | ✗ |
| S005.sigil | 30 | 0 | 0 | 0 | 0.0 | ✓ |
| S006.sigil | 30 | 0 | 0 | 0 | 0.0 | ✓ |
| T043.sigil | 500 | 15 | 28 | 162 | 79.6 | ✗ |
| T046.sigil | 500 | 14 | 26 | 61 | 51.8 | ✗ |
| T140.sigil | 122 | 15 | 24 | 36 | 34.6 | ✗ |
| T155.sigil | 500 | 11 | 20 | 141 | 64.2 | ✗ |
| T156.sigil | 500 | 13 | 20 | 63 | 36.0 | ✗ |
| T183.sigil | 500 | 28 | 47 | 163 | 43.0 | ✗ |
| T184.sigil | 500 | 33 | 52 | 167 | 37.2 | ✗ |
| T185.sigil | 500 | 18 | 28 | 96 | 30.2 | ✗ |
| T186.sigil | 500 | 26 | 37 | 85 | 26.0 | ✗ |
| T190.sigil | 32 | 8 | 8 | 13 | 12.4 | ⚠ |
| T191.sigil | 31 | 6 | 6 | 8 | 7.0 | ⚠ |
| T192.sigil | 500 | 7 | 9 | 55 | 46.1 | ✗ |
| T193.sigil | 500 | 10 | 17 | 33 | 38.5 | ✗ |
| T195.sigil | 96 | 12 | 13 | 30 | 17.1 | ⚠ |
| T196.sigil | 500 | 7 | 8 | 19 | 12.3 | ⚠ |
| T197.sigil | 342 | 7 | 11 | 67 | 65.2 | ✗ |
| T198.sigil | 500 | 1 | 1 | 2 | 52.2 | ✗ |
| T200.sigil | 500 | 12 | 15 | 44 | 25.7 | ✗ |
| T201.sigil | 36 | 7 | 8 | 10 | 10.4 | ⚠ |

## cve_corpus — per-fixture detail (solver=OFF)

| Fixture | n | Median (μs) | P90 (μs) | Max (μs) | CV % | Flag |
|---|---:|---:|---:|---:|---:|:-:|
| 01_cve_2021_44228_log4shell.sigil | 31 | 12 | 13 | 17 | 8.3 | ⚠ |
| 01_cve_2021_44228_log4shell_safe.sigil | 381 | 36 | 50 | 133 | 24.3 | ✗ |
| 02_cve_2017_5638_struts2_safe.sigil | 38 | 20 | 22 | 29 | 9.3 | ⚠ |
| 03_dao_reentrancy.sigil | 234 | 31 | 36 | 127 | 30.3 | ✗ |
| 03_dao_reentrancy_safe.sigil | 186 | 38 | 59 | 91 | 22.7 | ✗ |
| 04_cve_2022_22965_spring4shell_safe.sigil | 51 | 26 | 28 | 34 | 6.3 | ⚠ |
| 05_cve_2019_19781_citrix.sigil | 90 | 12 | 17 | 41 | 34.4 | ✗ |
| 05_cve_2019_19781_citrix_safe.sigil | 32 | 21 | 23 | 30 | 9.5 | ⚠ |
| 06_cve_2014_6271_shellshock_safe.sigil | 32 | 27 | 29 | 39 | 9.8 | ⚠ |
| 07_cve_2014_3704_drupalgeddon_safe.sigil | 30 | 27 | 29 | 32 | 4.7 | ✓ |
| 08_cve_2019_11932_whatsapp.sigil | 320 | 42 | 55 | 155 | 30.3 | ✗ |
| 08_cve_2019_11932_whatsapp_safe.sigil | 337 | 41 | 53 | 112 | 20.2 | ✗ |
| 09_cve_2017_1000353_jenkins_safe.sigil | 33 | 45 | 51 | 69 | 10.6 | ⚠ |
| 10_cve_2018_1002105_k8s.sigil | 51 | 15 | 17 | 27 | 11.8 | ⚠ |
| 10_cve_2018_1002105_k8s_safe.sigil | 30 | 27 | 29 | 32 | 4.4 | ✓ |

## z3_corpus — per-fixture detail (solver=OFF)

| Fixture | n | Median (μs) | P90 (μs) | Max (μs) | CV % | Flag |
|---|---:|---:|---:|---:|---:|:-:|
| 01_attenuation_at_call.sigil | 67 | 26 | 36 | 52 | 20.3 | ✗ |
| 02_attenuation_at_spawn.sigil | 41 | 30 | 33 | 45 | 11.6 | ⚠ |
| 03_attenuation_at_send.sigil | 93 | 39 | 45 | 65 | 11.6 | ⚠ |
| 04_handle_proof_gap.sigil | 47 | 17 | 19 | 34 | 15.0 | ⚠ |
| 05_region_proof_gap.sigil | 38 | 17 | 19 | 59 | 37.0 | ✗ |
| 06_negative_control.sigil | 116 | 40 | 61 | 101 | 22.8 | ✗ |
| 07_attenuation_at_return.sigil | 137 | 26 | 32 | 68 | 25.9 | ✗ |
| 08_rate_limit_inexpressible.sigil | 44 | 26 | 28 | 33 | 6.0 | ⚠ |
| 09_rate_limit_via_draw.sigil | 117 | 38 | 45 | 83 | 18.1 | ⚠ |
| 10_multi_party_approval.sigil | 215 | 41 | 50 | 82 | 16.1 | ⚠ |
| 11_time_bound_approval.sigil | 31 | 25 | 27 | 32 | 6.4 | ⚠ |
| 12_quorum_accumulation_wall.sigil | 215 | 37 | 48 | 143 | 23.7 | ✗ |
| 13_reference_monitor.sigil | 71 | 40 | 45 | 54 | 7.8 | ⚠ |
| 14_deadline_typed_cap_wall.sigil | 105 | 27 | 36 | 88 | 35.1 | ✗ |
| 15_per_query_stress.sigil | 500 | 154 | 219 | 562 | 29.5 | ✗ |
| 16_per_program_stress.sigil | 95 | 234 | 432 | 738 | 33.9 | ✗ |
| 17_m_of_n_quorum.sigil | 101 | 132 | 232 | 281 | 29.0 | ✗ |
| 18_inter_actor_3_of_3.sigil | 500 | 212 | 322 | 1037 | 32.6 | ✗ |
| 19_multi_branch_meet.sigil | 56 | 95 | 105 | 134 | 25.0 | ✗ |
| 20_deadline_subtyping.sigil | 137 | 21 | 35 | 64 | 28.6 | ✗ |
| 21_restrict_deadline.sigil | 43 | 16 | 17 | 20 | 6.1 | ⚠ |
| 22_deadline_composite.sigil | 32 | 28 | 30 | 44 | 10.6 | ⚠ |
| 23_multi_param_cap.sigil | 30 | 25 | 27 | 29 | 4.3 | ✓ |
| 24_multi_param_arity_mismatch.sigil | 31 | 16 | 16 | 19 | 5.4 | ⚠ |

