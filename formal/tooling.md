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

# Choose an explicit report path (the target must not already exist)
powershell -ExecutionPolicy Bypass -File formal/check-model.ps1 `
  -Scenario wal -Workers 4 `
  -ResultsPath formal/results/wal.result.json

# Skip result capture for an intentionally ephemeral local run
powershell -ExecutionPolicy Bypass -File formal/check-model.ps1 `
  -Scenario wal -NoResults
```

`-Workers N` selects TLC workers. `-Scenario NAME` runs one manifest entry.
`-KeepStates` preserves the unique temporary run directory after a successful
run. Failures after state-directory creation retain it for debugging; failures
before that point have no run state to preserve.

Runs that reach evidence initialization write a versioned JSON report by
default. The default destination is a collision-resistant, timestamped name
under `formal/results`; the runner
prints the absolute path at creation and finalization. `-ResultsPath FILE`
selects a different destination, with relative paths resolved from the
invocation directory. Both modes reserve a new file atomically and refuse to
overwrite an existing target. `-NoResults` is the explicit opt-out and cannot
be combined with `-ResultsPath`.

The runner creates parent directories, uses temporary-file replacement to
avoid exposing a partially written JSON document, and checkpoints the report
after each completed scenario. A TLC failure is recorded and still produces
the same nonzero script result as a run without capture. If the runner is
forcibly terminated before finalization, the last report can retain status
`running` instead of falsely claiming success.

Before downloading or launching tools, the runner validates the complete
manifest. Scenario names must be unique lowercase identifiers; tiers must be
exactly `smoke` or `full`; every entry must contain only `name`, `tier`,
`module`, and `config`; module/configuration values must be local leaf
filenames with the correct extension; and configurations may be registered
only once. Every `formal/*.cfg` file must be registered, so adding a model-check
configuration without assigning it to a scenario fails closed.

Each invocation copies every local `formal/*.tla` file and only the selected
scenario configurations into a unique temporary snapshot. The copied inputs
are marked read-only, hashed there, checked before and after every TLC process,
and TLC runs with that snapshot as its working directory. Consequently, an
edit to the working tree during a long run cannot change later scenarios or
make recorded source hashes disagree with the files TLC executed. Integrity
validation compares exact snapshot membership in addition to expected hashes;
an added, deleted, renamed, or modified snapshot entry fails the run.

The shared temporary tool directory is only a hash-validated download cache.
For every invocation, the runner copies the pinned JRE archive and TLA+ Tools
JAR into the unique run directory, freshly extracts the copied JRE archive,
and launches only those per-run files. It recursively inventories all files
and directories in that isolated tool snapshot and checks exact membership and
file hashes before and after each TLC scenario. This prevents another process
or later cache mutation from changing the toolchain used midway through a run.

Each report includes the name-sorted hashes of the copied TLA+ modules, counts
of copied modules/configurations, and hashes of `check-model.ps1`, the result
schema, and the exact manifest bytes that were parsed. Each scenario record
then contains:

- UTC start/completion timestamps and measured duration;
- TLC exit status, worker count, and coverage setting;
- the module and configuration names and SHA-256 hashes;
- pinned TLA+ Tools and JRE versions and artifact hashes, plus observed TLC and
  Java version strings and the actual per-run `java.exe` hash;
- TLC's fingerprint-polynomial index, random seed, and aril when printed; and
- generated states, distinct states, and completed-search depth when printed.

Fields derived from TLC output are `null` if TLC exits before emitting them or
if a future output format cannot be recognized. The report intentionally does
not embed TLC output, state files, or error traces; use `-KeepStates` when those
debugging artifacts are needed. The versioned schema and retention policy are
documented in [`results/README.md`](results/README.md).
Generated JSON reports under that directory are ignored by Git by default.
`formal/results/h1-full.result.json` is the intentionally retained H1
full-suite artifact; regenerate it whenever a bound runner, schema, model,
configuration, manifest, or tool input changes.

The execution snapshot intentionally includes all local TLA+ modules rather
than attempting to infer a minimal import closure. This is conservative:
unrelated local modules can change the report hash set, but no local `EXTENDS`
or `INSTANCE` dependency is silently omitted. Standard modules are supplied by
the hash-pinned TLA+ Tools JAR. Successful runs remove the snapshot unless
`-KeepStates` is set; its hashes remain in the report as the durable provenance
record.

The report's tool snapshot includes entry counts, the copied JRE archive and
TLA+ Tools JAR hashes, the actual `java.exe` hash, and a complete tree digest.
The digest is SHA-256 over name-sorted UTF-8 lines of the form `D<TAB>path` for
directories and `F<TAB>path<TAB>sha256` for files, with an LF after every line.
`invocation.workingDirectory` is repository-relative (`.` at repository root)
or `<outside-repository>`, never an absolute identifying host path.

Before a root report can be marked `passed`, the runner compares the selected
manifest sequence with both its internal completion records and the serialized
scenario sequence. All counts, names, tiers, statuses, exit codes, and errors
must agree. Schema version `1.3.0` independently requires a completed,
nonempty passed root whose scenarios all passed with exit status zero and null
errors.

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
host, observed complete 13-scenario provenance runs took about 24--45 minutes,
depending on load. The schema-v1.1 baseline run took about 24 minutes; its
composed retry scenario took about 9 minutes 44 seconds and its two-request
composed prefix about 3 minutes 21 seconds. Neither belongs in the smoke tier.

## Reproducibility boundary

The bootstrap currently supports Windows x64 and requires network access on
the first run. It downloads pinned Temurin JRE `21.0.11+10` and TLA+ Tools
`v1.7.4`, verifies their SHA-256 hashes, and caches them under the system
temporary directory. Cache access is serialized with a named mutex; each
model-check run uses a unique state directory, copied JAR, and fresh JRE
extraction.

Linux/macOS bootstrap or a pinned container remains an artifact-engineering
task. The model and configurations themselves are platform-independent TLA+.

Coverage is optional because full expression coverage is verbose. It is useful
for detecting scenario-specific unreachable actions; zero coverage in one
scenario is not necessarily a defect when another scenario is designed to
exercise that branch.
