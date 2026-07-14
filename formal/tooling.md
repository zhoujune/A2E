# Model-Checking Tooling

`check-model.ps1` runs the scenarios declared in `model-suite.json`.

## Commands

```powershell
# Fast regression scenarios
powershell -ExecutionPolicy Bypass -File formal/check-model.ps1 -Suite smoke

# Smoke plus all full scenarios
powershell -ExecutionPolicy Bypass -File formal/check-model.ps1

# Include TLC action/expression coverage
powershell -ExecutionPolicy Bypass -File formal/check-model.ps1 -Coverage

# Run one named manifest scenario
powershell -ExecutionPolicy Bypass -File formal/check-model.ps1 `
  -Scenario idempotent-retry -Coverage

# Also preserve a machine-readable run report
powershell -ExecutionPolicy Bypass -File formal/check-model.ps1 `
  -Scenario wal -Workers 4 `
  -ResultsPath formal/results/wal.result.json
```

`-Workers N` selects TLC workers. `-Scenario NAME` runs one manifest entry.
`-KeepStates` preserves the unique temporary run directory after a successful
run; failed runs retain it automatically for debugging.

`-ResultsPath FILE` opts into a versioned JSON report. A relative path is
resolved from the directory in which the command was invoked. The runner
creates parent directories, uses temporary-file replacement to avoid exposing
a partially written JSON document, and updates `FILE` after each completed
scenario. A TLC failure is recorded and still produces the same nonzero script
result as a run without this option. If the runner is forcibly terminated
before finalization, the last report can retain status `running` instead of
falsely claiming success.

Each report includes a name-sorted snapshot of every local `formal/*.tla`
source, conservatively covering modules reached through `EXTENDS` or
`INSTANCE`, plus hashes of `check-model.ps1`, the result schema, and the suite
manifest. Each scenario record then contains:

- UTC start/completion timestamps and measured duration;
- TLC exit status, worker count, and coverage setting;
- the module and configuration names and SHA-256 hashes;
- pinned TLA+ Tools and JRE versions and artifact hashes, plus observed TLC and
  Java version strings;
- TLC's fingerprint-polynomial index, random seed, and aril when printed; and
- generated states, distinct states, and completed-search depth when printed.

Fields derived from TLC output are `null` if TLC exits before emitting them or
if a future output format cannot be recognized. The report intentionally does
not embed TLC output, state files, or error traces; combine `-ResultsPath` with
`-KeepStates` when those debugging artifacts are needed. The versioned schema
and retention policy are documented in [`results/README.md`](results/README.md).
Generated JSON reports under that directory are ignored by Git by default.

The source snapshot intentionally includes all local TLA+ modules rather than
attempting to infer a minimal import closure. This is conservative: unrelated
local modules can change the report hash set, but no local `EXTENDS` or
`INSTANCE` dependency is silently omitted. Standard modules are supplied by
the hash-pinned TLA+ Tools JAR.

The smoke tier contains the broad broker smoke model, a focused idempotent
retry model, the typed Journal, two Journal-to-Broker refinement scenarios,
the typed WAL, the uncontrolled composed WAL/Broker scenario, and the focused
two-capability Broker scenario. The full tier adds the two-request/two-capability
composed prefix, the composed idempotent-retry product, and the larger
deduplicated, idempotent, and read-only Broker configurations.

The two-request composed scenario uses `MaxJournalLength = 5`. It checks
cross-request/cross-capability interleavings and recovery quarantine, but a
normal terminal lifecycle needs six records; terminal branches are covered by
the existing one-request composed scenarios. On the current 4-worker Windows
host, observed complete 13-scenario provenance runs took about 24--36 minutes,
depending on load. The latest schema-v1.1 run took about 24 minutes; its
composed retry scenario took about 9 minutes 44 seconds and its two-request
composed prefix about 3 minutes 21 seconds. Neither belongs in the smoke tier.

## Reproducibility boundary

The bootstrap currently supports Windows x64 and requires network access on
the first run. It downloads pinned Temurin JRE `21.0.11+10` and TLA+ Tools
`v1.7.4`, verifies their SHA-256 hashes, and caches them under the system
temporary directory. Dependency installation is serialized with a named mutex;
each model-check run uses a unique state directory.

Linux/macOS bootstrap or a pinned container remains an artifact-engineering
task. The model and configurations themselves are platform-independent TLA+.

Coverage is optional because full expression coverage is verbose. It is useful
for detecting scenario-specific unreachable actions; zero coverage in one
scenario is not necessarily a defect when another scenario is designed to
exercise that branch.
