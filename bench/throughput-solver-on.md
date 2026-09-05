# Compile throughput — solver=ON

Convergence: per-fixture sample count is bounded above by 500, minimum 30, terminates when trailing CV < 5.0%.
Fixtures with CV ≥ 20% are dropped from per-corpus medians/totals (✗ flag).

## Per-corpus summary (solver=ON)

| Corpus | Files measured | Dropped (CV>20%) | Median (μs) | P90 (μs) | Total (μs) |
|---|---:|---:|---:|---:|---:|
| fixtures | 19 | 11 | 8 | 11 | 135 |
| cve_corpus | 3 | 12 | 5001 | 6596 | 10204 |
| z3_corpus | 4 | 20 | 5441 | 9360 | 12722 |

## fixtures — per-fixture detail (solver=ON)

| Fixture | n | Median (μs) | P90 (μs) | Max (μs) | CV % | Flag |
|---|---:|---:|---:|---:|---:|:-:|
| E003.sigil | 98 | 9 | 11 | 16 | 16.3 | ⚠ |
| N007.sigil | 50 | 3 | 4 | 20 | 68.0 | ✗ |
| N008.sigil | 64 | 14 | 17 | 137 | 90.9 | ✗ |
| N009.sigil | 30 | 5 | 5 | 6 | 3.6 | ✓ |
| N011.sigil | 52 | 1 | 1 | 7 | 74.6 | ✗ |
| R003.sigil | 31 | 8 | 8 | 12 | 8.8 | ⚠ |
| R004.sigil | 30 | 13 | 13 | 16 | 4.4 | ✓ |
| R006.sigil | 30 | 8 | 8 | 9 | 3.1 | ✓ |
| S004.sigil | 30 | 0 | 0 | 0 | 0.0 | ✓ |
| S005.sigil | 30 | 0 | 0 | 0 | 0.0 | ✓ |
| S006.sigil | 30 | 0 | 0 | 0 | 0.0 | ✓ |
| T043.sigil | 500 | 11 | 15 | 47 | 26.4 | ✗ |
| T046.sigil | 56 | 9 | 9 | 11 | 6.4 | ⚠ |
| T140.sigil | 31 | 10 | 10 | 14 | 8.5 | ⚠ |
| T155.sigil | 79 | 10 | 11 | 17 | 11.3 | ⚠ |
| T156.sigil | 218 | 12 | 17 | 28 | 22.6 | ✗ |
| T183.sigil | 500 | 27 | 42 | 132 | 32.3 | ✗ |
| T184.sigil | 500 | 32 | 44 | 172 | 35.3 | ✗ |
| T185.sigil | 62 | 14 | 16 | 26 | 17.0 | ⚠ |
| T186.sigil | 489 | 20 | 34 | 98 | 34.4 | ✗ |
| T190.sigil | 402 | 8 | 9 | 15 | 10.8 | ⚠ |
| T191.sigil | 33 | 6 | 7 | 8 | 7.5 | ⚠ |
| T192.sigil | 32 | 6 | 7 | 11 | 17.7 | ⚠ |
| T193.sigil | 500 | 7 | 11 | 93 | 66.9 | ✗ |
| T195.sigil | 62 | 12 | 13 | 75 | 60.7 | ✗ |
| T196.sigil | 500 | 7 | 8 | 23 | 18.5 | ⚠ |
| T197.sigil | 470 | 6 | 7 | 17 | 12.9 | ⚠ |
| T198.sigil | 45 | 0 | 1 | 1 | 217.5 | ✗ |
| T200.sigil | 37 | 9 | 10 | 14 | 10.0 | ⚠ |
| T201.sigil | 31 | 7 | 7 | 9 | 5.6 | ⚠ |

## cve_corpus — per-fixture detail (solver=ON)

| Fixture | n | Median (μs) | P90 (μs) | Max (μs) | CV % | Flag |
|---|---:|---:|---:|---:|---:|:-:|
| 01_cve_2021_44228_log4shell.sigil | 31 | 12 | 13 | 24 | 17.4 | ⚠ |
| 01_cve_2021_44228_log4shell_safe.sigil | 500 | 4685 | 6559 | 10060 | 22.8 | ✗ |
| 02_cve_2017_5638_struts2_safe.sigil | 500 | 5281 | 7777 | 13137 | 27.1 | ✗ |
| 03_dao_reentrancy.sigil | 500 | 5119 | 7044 | 10892 | 21.2 | ✗ |
| 03_dao_reentrancy_safe.sigil | 500 | 5001 | 6463 | 9402 | 20.0 | ⚠ |
| 04_cve_2022_22965_spring4shell_safe.sigil | 500 | 5281 | 7036 | 10317 | 23.2 | ✗ |
| 05_cve_2019_19781_citrix.sigil | 77 | 10 | 18 | 34 | 39.8 | ✗ |
| 05_cve_2019_19781_citrix_safe.sigil | 500 | 4962 | 6820 | 9271 | 24.1 | ✗ |
| 06_cve_2014_6271_shellshock_safe.sigil | 500 | 5093 | 6899 | 9842 | 23.2 | ✗ |
| 07_cve_2014_3704_drupalgeddon_safe.sigil | 500 | 5190 | 7645 | 19554 | 30.3 | ✗ |
| 08_cve_2019_11932_whatsapp.sigil | 500 | 5383 | 7452 | 11325 | 23.1 | ✗ |
| 08_cve_2019_11932_whatsapp_safe.sigil | 500 | 5191 | 6596 | 9904 | 19.4 | ⚠ |
| 09_cve_2017_1000353_jenkins_safe.sigil | 500 | 4625 | 6188 | 9492 | 20.2 | ✗ |
| 10_cve_2018_1002105_k8s.sigil | 220 | 22 | 29 | 127 | 49.1 | ✗ |
| 10_cve_2018_1002105_k8s_safe.sigil | 500 | 5263 | 7159 | 10210 | 23.7 | ✗ |

## z3_corpus — per-fixture detail (solver=ON)

| Fixture | n | Median (μs) | P90 (μs) | Max (μs) | CV % | Flag |
|---|---:|---:|---:|---:|---:|:-:|
| 01_attenuation_at_call.sigil | 500 | 5441 | 7681 | 16083 | 26.3 | ✗ |
| 02_attenuation_at_spawn.sigil | 500 | 5288 | 7141 | 11813 | 23.5 | ✗ |
| 03_attenuation_at_send.sigil | 500 | 5281 | 7394 | 11274 | 24.3 | ✗ |
| 04_handle_proof_gap.sigil | 500 | 4902 | 6727 | 12922 | 24.2 | ✗ |
| 05_region_proof_gap.sigil | 500 | 4589 | 6007 | 9932 | 20.1 | ✗ |
| 06_negative_control.sigil | 500 | 5441 | 7119 | 10890 | 20.0 | ⚠ |
| 07_attenuation_at_return.sigil | 500 | 5274 | 7189 | 11856 | 22.9 | ✗ |
| 08_rate_limit_inexpressible.sigil | 500 | 5530 | 7390 | 10023 | 22.9 | ✗ |
| 09_rate_limit_via_draw.sigil | 500 | 5429 | 7528 | 10354 | 24.0 | ✗ |
| 10_multi_party_approval.sigil | 500 | 5632 | 8194 | 12485 | 27.3 | ✗ |
| 11_time_bound_approval.sigil | 500 | 4942 | 6684 | 10733 | 24.0 | ✗ |
| 12_quorum_accumulation_wall.sigil | 500 | 5505 | 7672 | 10881 | 23.6 | ✗ |
| 13_reference_monitor.sigil | 500 | 5960 | 8181 | 12562 | 22.7 | ✗ |
| 14_deadline_typed_cap_wall.sigil | 500 | 5350 | 6874 | 9765 | 21.1 | ✗ |
| 15_per_query_stress.sigil | 500 | 7533 | 9914 | 13490 | 22.8 | ✗ |
| 16_per_program_stress.sigil | 500 | 9110 | 11319 | 14601 | 20.3 | ✗ |
| 17_m_of_n_quorum.sigil | 500 | 6214 | 8599 | 12528 | 24.2 | ✗ |
| 18_inter_actor_3_of_3.sigil | 500 | 7223 | 9360 | 12107 | 18.8 | ⚠ |
| 19_multi_branch_meet.sigil | 500 | 5622 | 7372 | 11031 | 21.0 | ✗ |
| 20_deadline_subtyping.sigil | 58 | 32 | 35 | 73 | 17.5 | ⚠ |
| 21_restrict_deadline.sigil | 37 | 26 | 28 | 36 | 8.3 | ⚠ |
| 22_deadline_composite.sigil | 500 | 5558 | 7197 | 13119 | 23.0 | ✗ |
| 23_multi_param_cap.sigil | 500 | 5823 | 8238 | 15696 | 28.4 | ✗ |
| 24_multi_param_arity_mismatch.sigil | 364 | 27 | 31 | 154 | 39.7 | ✗ |

