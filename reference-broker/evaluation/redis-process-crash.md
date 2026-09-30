# Redis Process-Crash Experiment

This campaign tests whether request-wide failure coverage changes an exported
decision after a real broker process crash while an independent service keeps
running. It is process-crash evidence for the reference broker, not a proof of
Redis correctness or production adapter conformance.

## Reproduce

Requirements: Linux or WSL, Python 3.9+, Rust 1.96, a Redis 7.2.5 source archive,
and a compiled redis-server. The retained build used the official archive
redis-7.2.5.tar.gz (SHA-256:
5981179706f8391f03be91d951acafaeda91af7fac56beffb2701963103e423d).
Redis ran on a private Unix socket with TCP disabled, AOF enabled, and
appendfsync always. Each scenario used an isolated Redis process and data
directory.

Run from the repository root:

    python3 reference-broker/evaluation/run_redis_process_crash.py \
      --cargo /path/to/rust-1.96/bin/cargo \
      --redis-server /path/to/redis-7.2.5/src/redis-server \
      --redis-source-archive /path/to/redis-7.2.5.tar.gz \
      --output reference-broker/evaluation/results/redis-process-crash.json

The runner builds the full broker and a temporary mutant from identical source.
The mutant removes just the Idempotent branch that returns
Unknown(NonConclusiveFailure) when prior attempts are not all failures. The
production source tree is not modified by the mutation. In the effect-completed
case, a local proxy forwards SADD to Redis, waits until Redis has applied it,
then withholds the reply; the controller kills the broker with SIGKILL. In the
zero-effect pair, the broker is killed after Start but before sending SADD.
After restart, Redis ACL revokes SADD, so the retry receives NOPERM. The
independent SISMEMBER oracle reads service state before and after the crash and
at the decision boundary. The observer gate records WAL prefixes and pauses
before terminal append; it does not validate a verified kernel or change the
classifier.

## Retained Result

The JSON report records eight executions, tool versions, source hashes,
state-oracle answers, terminal decisions, WAL hashes, and run times. The
reviewer package includes the eight per-case `case.json` oracle records,
broker WALs, pre-terminal records, decision output, Redis AOF/logs, and the
single-branch ablation patch under
`reference-broker/evaluation/evidence/redis-process-crash/`. The packaged
`case.json` files omit local command paths and process IDs; their outcomes,
oracle readings, and WAL hashes are unchanged.

The paired runs have byte-identical initial and pre-terminal WALs within each
broker variant. The retained report has status passed: the full broker
decisions are Unknown for both zero- and one-effect
states; the mutant returns Fail for both, which is unsafe in the one-effect
case. Both variants preserve their conclusive failure and success controls.
Reopening terminal requests makes zero service calls.

Scope is serialized local execution with Redis alive while the broker process
is killed. The campaign does not test machine power loss, Redis process failure,
network deployment, concurrent requests, or formal refinement of Redis or the
adapter. Redis was isolated in a separate process for each case; the broker
alone was SIGKILLed at the controlled boundary. Although Redis used AOF and
appendfsync always, the experiment does not test Redis recovery or establish
that either service state or broker WAL survives power loss.
