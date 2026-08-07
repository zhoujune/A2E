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
