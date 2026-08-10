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

These single-run numbers validate the harness and expose its accounting. A
zero recovery time for the Direct workload means that the ablation provides no
recovery mechanism, not instantaneous durable recovery.

## Controlled repeated RQ2 run

`rq2-repeated-linux.json` uses five warmups, thirty measured repetitions, 500
requests per primary workload, 50 requests per retry workload, a 25 ms gap
between measured runs, and CPU affinity `{0}`. Its SHA-256 is
`7acb2ee7dbe2b0a06d6a1c5e7383661e5c91c1a1dd4e91ad886fb70f3f7a2ba3`.

| Workload | Mean latency (ms) | 95% interval (ms) | Mean requests/s | Mean recovery (ms) |
|---|---:|---:|---:|---:|
| Mediated | 0.464 | 0.452-0.475 | 2,165.87 | 1.268 |
| Direct | below 0.001 | below 0.001 | 13,892,373.93 | not applicable |
| Journaled at-least-once | 0.144 | 0.139-0.148 | 7,011.15 | 0.020 |

Retry workloads averaged 0.588 ms for mediated Idempotent, 0.592 ms for
mediated Deduplicated, and 0.285 ms for journaled at-least-once. The two
contract-bearing adapters retained one abstract effect per request; the
contract-free baseline retained one extra effect per request.

This is still a local overlayfs measurement with fixed workload order and no
remote service or physical-device controls. It is a reproducible artifact
baseline, not a universal systems-performance claim.

## Paired storage-sensitivity run

`rq2-repeated-server-overlayfs.json` and `rq2-repeated-server-tmpfs.json`
repeat the controlled protocol at source revision
`de33054c245fc136e37f4f56c5acc7ef36658604`. Both reports use the same release
binary (SHA-256
`6f7db9c994dad64bc76f07d2c44ad8bd6c45f6fd65b789fecba039c9df3d3d0f`),
Rust 1.96.0, host, CPU affinity `{0}`, workload sizes, and repetition counts.
Only the temporary-WAL filesystem changes.

| Temporary filesystem | Mediated mean (95% interval), ms | Mediated requests/s | Journaled mean (95% interval), ms | Journaled requests/s |
|---|---:|---:|---:|---:|
| overlayfs | 0.391 (0.382-0.399) | 2,567.99 | 0.116 (0.112-0.120) | 8,692.86 |
| tmpfs | 0.0358 (0.0353-0.0363) | 27,934.98 | 0.001423 (0.001413-0.001433) | 683,653.60 |

| Temporary filesystem | Idempotent retry mean, ms | Deduplicated retry mean, ms | Journaled retry mean, ms |
|---|---:|---:|---:|
| overlayfs | 0.479 | 0.492 | 0.243 |
| tmpfs | 0.0164 | 0.0165 | 0.00286 |

The overlayfs means are 10.9 times the tmpfs mean for mediated requests and
81.5 times the tmpfs mean for the two-record journal. This demonstrates that
the local result is storage-path sensitive. It does not establish a universal
ratio: tmpfs does not survive a host restart, and `sync_data` on tmpfs is not a
physical durable-media flush. In every measured run the contract-bearing
retry workloads still made two physical invocations and one abstract effect
per request, while the journaled at-least-once workload made two effects.

The report SHA-256 values are
`90826f72651fe7cde2838bde16176cb93723405d04444e573259bc6bf0596fee`
for overlayfs and
`20cff26b732a91ef7a834092d8b388cf457420ba1e188d45e80ea92820f044a9`
for tmpfs. The server endpoint resolved to the same container hostname as the
older retained baseline, so these files add a paired storage condition but do
not count as independent-host replication.

## Physical-storage follow-up

`rq2-repeated-server-ext4.json` repeats the same protocol at source revision
`01fbcddda570e53f95c4f9bfcdc4d01f7f77617f`, with the temporary WAL under
`/nix`. The report records `temporary_mount_source` `/dev/nvme3n1`, target
`/nix`, and mount filesystem `ext4`; the generic `stat` family is
`ext2/ext3`. It uses the same release binary as the paired run, Rust 1.96,
CPU affinity `{0}`, five warmups, thirty repetitions, and 500/50 requests.

| Temporary filesystem | Mediated mean (95% interval), ms | Mediated requests/s | Journaled mean (95% interval), ms | Journaled requests/s |
|---|---:|---:|---:|---:|
| NVMe-backed ext4 | 0.456 (0.443-0.469) | 2,206.57 | 0.141 (0.136-0.146) | 7,165.82 |

The retry means were 0.588 ms for mediated Idempotent, 0.588 ms for mediated
Deduplicated, and 0.277 ms for journaled at-least-once; mediated recovery
averaged 1.330 ms. The contract-bearing retry workloads still retained one
abstract effect per request, while the journaled ablation retained one extra
effect per request.

The report SHA-256 is
`0e23518d31c2639859e251560e25ed8a5393ff15aa6da3bf17b77a1d1a868de3`.
This is evidence for a physical-storage condition and is materially different
from tmpfs, but `/nix` is a Kubernetes `emptyDir` on the same server hostname.
It therefore does not establish independent-host replication or persistence
across pod deletion.

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
