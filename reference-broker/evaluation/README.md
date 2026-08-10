# RQ1/RQ2 evaluation harness

The `evaluate` binary reruns the M4 crash matrix and three local
microbenchmarks, then emits a versioned JSON report conforming to
`evaluation-report.schema.v1.json`.

## Run

From `reference-broker/`:

```sh
PROVEAI_SOURCE_REVISION="$(git rev-parse HEAD)" \
  cargo run --release --bin evaluate -- \
  --iterations 100 \
  --output evaluation/results/rq1-rq2-linux.json
```

Validate the retained report and its cross-field accounting using only the
Python standard library:

```sh
python3 evaluation/validate_report.py \
  evaluation/results/rq1-rq2-linux.json
```

The versioned JSON Schema can additionally be checked with any Draft 2020-12
validator. For example, when Python `jsonschema` is available:

```sh
python3 -m jsonschema \
  -i evaluation/results/rq1-rq2-linux.json \
  evaluation/evaluation-report.schema.v1.json
```

## RQ1 fields

The report contains the Cartesian product of three adapters and seven crash
sites. Every case is rerun from a fresh WAL. `passed` requires:

- exactly one terminal record;
- a terminal attempt within the configured retry bound;
- exact `Start -> Arm -> Prepare -> Authorize` ancestry for every invocation;
- the adapter-specific abstract-effect oracle; and
- the expected conservative Unknown/commit classification.

Stale-delivery rejection is a separate executable check that also requires no
WAL change and preservation of the current executor slot.

## RQ2 workloads

The primary workloads use the same number of logical requests:

- `mediated`: the M4 broker with `sync_data` after every protocol record;
- `direct`: an in-process effect with no durability or recovery semantics; and
- `journaled_at_least_once`: a two-record Start/result journal with
  `sync_data`, but no adapter effect contract.

The retry scenarios inject one ambiguous first result. The Idempotent and
Deduplicated broker adapters perform two physical invocations but one abstract
mutation. The journaled at-least-once ablation performs two invocations and two
effects, exposing the semantic difference rather than treating it only as a
timing baseline.

Reported timings are single-process local microbenchmarks, not production
performance claims. They include filesystem and host noise, do not model a
network service, and must be regenerated on the artifact evaluator's machine.
The retained report records its hostname, target, Rust version, release/debug
profile, package version, and source revision.

## Repeated RQ2 protocol

Build once in release mode, then run the repetition controller. On Linux,
`taskset` can pin the runner and every child benchmark to one CPU:

```sh
cargo build --release --bin evaluate
PROVEAI_SOURCE_REVISION="$(git rev-parse HEAD)" \
  taskset -c 0 python3 evaluation/run_repeated_rq2.py \
  --binary target/release/evaluate \
  --iterations 500 \
  --warmups 5 \
  --repetitions 30 \
  --output evaluation/results/rq2-repeated-linux.json
python3 evaluation/validate_repeated_rq2.py \
  evaluation/results/rq2-repeated-linux.json
```

The controller starts a fresh process with fresh temporary WALs for every
warmup and measured run. It retains all run-level samples and reports mean,
median, standard deviation, range, and a 95% normal-approximation interval for
every measurement. The report also binds the benchmark binary hash, CPU
affinity, kernel, temporary-filesystem type, Python/Rust versions, and source
revision. When Linux `findmnt` is available, it additionally records the
temporary mount's backing source, target, and filesystem type. Fixed within-run
workload order and local synchronous effects remain explicit limitations.

Set `TMPDIR` before invoking the controller to select a temporary-WAL storage
condition. The retained `rq2-repeated-server-overlayfs.json` and
`rq2-repeated-server-tmpfs.json` reports use identical source, binary, host,
CPU affinity, and protocol settings. The tmpfs report is a storage-cost control,
not durable-media evidence, because tmpfs does not survive a host restart.
Validate each retained report independently with `validate_repeated_rq2.py`.

## RQ3 proof effort

Generate source, proof-function, obligation-delta, and retained verification-time
measurements from the hash-bound Verus report:

```sh
python3 evaluation/generate_rq3.py \
  --output evaluation/results/rq3-proof-effort.json
python3 evaluation/validate_rq3.py \
  evaluation/results/rq3-proof-effort.json
```

`rq3-adapter-manifest.v1.json` assigns targets to the shared framework and the
three adapters. The generator verifies every source hash before measuring it.
Verification durations include dependency rechecking, while contribution
deltas are the retained non-duplicated obligation measure. Person-hours are
`null` because no contemporaneous time log exists.

## RQ4 fault classification

`rq4-fault-matrix.v1.json` covers the product of three M4 adapters and the six
required failure windows. Validate coverage and required safety/availability
explanations with:

```sh
python3 evaluation/validate_rq4.py \
  evaluation/rq4-fault-matrix.v1.json
```

The matrix explicitly marks `send_to_linearization` as an adapter-contract
boundary because M4's synchronous adapter call has no internal crash hook. The
recovery-interruption cells are backed by `tests/recovery_interruption.rs`.
