# Retained RQ1/RQ2 baseline

`rq1-rq2-linux.json` is the first retained schema-v1 run of the M4 evaluation
harness.

- Source revision: `702a2537ab13bf79e069b34504388294211bfde7`
- Target: `x86_64-linux`
- Rust: `rustc 1.96.0 (ac68faa20 2026-05-25)`
- Profile: release
- Logical CPUs visible: 36
- Primary workload: 100 requests
- Retry workload: 10 requests
- SHA-256: `f76624af0d936769e6318852b470dd7be043c402eda3f05ff1abf897172d4645`

RQ1 reran all 21 adapter/crash-site combinations. All passed terminal
uniqueness, retry-bound, authorization-ancestry, expected-terminal, and
adapter-effect checks; stale-delivery rejection also passed.

The retained single-host RQ2 measurements are:

| Workload | Mean latency (ns) | P95 (ns) | Requests/s | WAL bytes | Flushes | Recovery (ns) |
|---|---:|---:|---:|---:|---:|---:|
| Mediated | 414,883 | 449,469 | 2,409.603 | 27,500 | 600 | 221,069 |
| Direct | 32 | 40 | 14,064,697.609 | 0 | 0 | 0 |
| Journaled at-least-once | 120,894 | 141,049 | 8,267.108 | 4,200 | 200 | 15,630 |

In the ten-request ambiguous-result workloads, both mediated retry-safe
adapters made 20 physical invocations but only 10 abstract mutations. The
journaled at-least-once ablation made 20 invocations and 20 effects, including
10 duplicate effects.

These numbers validate the harness and expose its accounting; they are not yet
paper-grade performance results. There are no warmups, repeated independent
runs, confidence intervals, remote services, or storage-device controls. A
zero recovery time for the Direct workload means that the ablation provides no
recovery mechanism, not instantaneous durable recovery.

## RQ3 and RQ4

`rq3-proof-effort.json` was generated from source revision
`d1771c7b365d1bfd0cf3fbe747c339a39ec9e1a1` and the retained 56-target Verus
report. Its SHA-256 is
`70c16dbaeb29d55e27edf213a5426fcb0c0f522ab059078e29767bc1f4b10509`.

| Adapter evidence | Targets | Source lines | Public proof functions | Non-duplicated obligation delta | Retained verification (ms) |
|---|---:|---:|---:|---:|---:|
| Idempotent EnsureMember | 5 | 12,879 | 121 | 181 | 542,501 |
| ReadOnly environment sample | 1 | 4,454 | 47 | 61 | 139,501 |
| Deduplicated keyed decision | 6 | 8,774 | 86 | 145 | 895,215 |

The shared T6-D0/E0/C0/S0 framework contains 55 public proof functions and
contributes 57 non-duplicated obligations. Target time and source volume include
dependency-layer rechecking; they are reproducibility costs, not independent
authoring costs. Person-hours remain unreported.

The RQ4 matrix covers 18 adapter/fault-window cells. Its SHA-256 is
`1459bbce3ae095ea0d399cfc2a91f82bf15e3e65dbbd6b27f5d583b246dacd23`.
The matrix distinguishes executable crash evidence, adapter-contract reasoning,
and the send/linearization point that M4 cannot observe internally.
