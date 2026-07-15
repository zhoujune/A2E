# Model-Check Result Artifacts

This directory contains the schema for machine-readable reports from
`formal/check-model.ps1`. The runner creates a uniquely named report here by
default. `h1-full.result.json` is the intentionally retained H1 full-suite
artifact; other generated reports remain ignored. A report is evidence only
for the exact runner, schema, module, configuration, and tool hashes recorded
by its invocation. Regenerate the retained artifact after any bound input
changes rather than editing it by hand.

Create a local report from the repository root with:

```powershell
powershell -ExecutionPolicy Bypass -File formal/check-model.ps1 `
  -Scenario wal -Workers 4
```

The command prints the generated report path. `-ResultsPath` can select another
new path, but the runner never overwrites an existing artifact. `-NoResults`
explicitly disables capture for an ephemeral run. Generated reports other than
the named H1 artifact are ignored by Git. Preserve a report intentionally
alongside a release or artifact bundle only after checking its `status`, input
hashes, and scenario selection. `schema.json` defines format version `1.3.0`.

The runner uses temporary-file replacement and checkpoints the report after
every completed scenario. Root status `running` means the process did not reach
normal finalization; `failed` can include completed earlier scenarios and the
failing scenario's nonzero exit status. Metrics parsed from TLC output are
nullable so an early tool failure is not mistaken for a zero-state
exploration. Schema conditionals require a `passed` root to be completed and
contain at least one scenario, with every scenario itself `passed`, exit status
zero, and no error. The runner separately checks that the reported scenario
sequence exactly matches the selected manifest entries before assigning root
status `passed`.

Before TLC starts, the runner validates the complete manifest and rejects
duplicate scenario names/configuration registrations, invalid tiers or paths,
missing inputs, and every unregistered `formal/*.cfg` file. It then copies all
local TLA+ modules and the selected configurations into a unique temporary
directory, marks them read-only, and checks their hashes before and after each
scenario. The check compares exact directory membership as well as content
hashes, so added files fail the run just like deleted or modified inputs. TLC
executes only from this frozen copy.

The shared tool directory is only a hash-validated download cache. Every run
copies the pinned JRE archive and TLA+ Tools JAR into its unique state
directory, freshly extracts that JRE, and recursively inventories the complete
per-run tool tree. The runner checks exact tool-tree membership and file hashes
before and after every scenario. The report records the aggregate tree digest,
entry counts, copied archive/JAR hashes, and the actual `java.exe` hash. The
tree digest is SHA-256 over name-sorted UTF-8 inventory lines: `D<TAB>path` for
a directory and `F<TAB>path<TAB>sha256` for a file, each terminated by LF.

The report hashes the runner and this schema in addition to the exact manifest
bytes parsed, selected module/configuration copies, complete copied TLA source
set, and isolated per-run tool snapshot. The runner checks that its own file,
the schema, and the manifest remain at those hashes around every scenario. The
recorded seed and fingerprint-polynomial
index identify TLC's randomized fingerprinting choices; they do not by
themselves make worker scheduling or wall-clock duration deterministic.
`modelInputs` is a name-sorted, conservative snapshot of every copied
`formal/*.tla` file, so imported local modules are covered even though the
runner does not attempt to infer an exact `EXTENDS`/`INSTANCE` closure.
Together with the selected configuration, manifest, pinned tool, and runtime
hashes, it records the executed source-snapshot boundary. Standard modules come
from the hash-pinned TLA+ Tools JAR.

`invocation.workingDirectory` is repository-relative (`.` at repository root)
or the literal `<outside-repository>`; reports do not disclose an absolute host
path or user profile name.
