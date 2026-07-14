# Model-Check Result Artifacts

This directory contains the schema for optional machine-readable reports from
`formal/check-model.ps1`. It deliberately contains no checked-in successful-run
example: a report is evidence only for the exact module, configuration, and
tool hashes recorded by an actual invocation.

Create a local report from the repository root with:

```powershell
powershell -ExecutionPolicy Bypass -File formal/check-model.ps1 `
  -Scenario wal -Workers 4 `
  -ResultsPath formal/results/wal.result.json
```

Reports in this directory are ignored by Git. Preserve a report intentionally
alongside a release or artifact bundle only after checking its `status`, input
hashes, and scenario selection. `schema.json` defines format version `1.1.0`.

The runner uses temporary-file replacement and checkpoints the report after
every completed scenario. Root status `running` means the process did not reach
normal finalization; `failed` can include completed earlier scenarios and the
failing scenario's nonzero exit status. Metrics parsed from TLC output are
nullable so an early tool failure is not mistaken for a zero-state
exploration.

The report hashes the runner and this schema in addition to the manifest,
selected module/configuration, complete local TLA source snapshot, and pinned
tool artifacts. The recorded seed and fingerprint-polynomial index identify
TLC's randomized fingerprinting choices; they do not by themselves make worker
scheduling or wall-clock duration deterministic. `modelInputs` is a name-sorted,
conservative snapshot of every `formal/*.tla` file, so imported local modules
are covered even though the runner does not attempt to infer an exact
`EXTENDS`/`INSTANCE` closure. Together with the selected configuration,
manifest, pinned tool, and runtime hashes, it records the run's source-snapshot
boundary. Standard modules come from the hash-pinned TLA+ Tools JAR.
