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
