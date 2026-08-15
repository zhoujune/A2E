[CmdletBinding()]
param(
    [string]$ReportPath = "",
    [switch]$NoReport,
    [string]$OfflineBundleRoot = ""
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$lockPath = Join-Path $scriptDir "toolchain.lock.json"
$resultsDir = Join-Path $scriptDir "results"
$schemaPath = Join-Path $resultsDir "verification-report.schema.v1.json"
$script:PathComparison =
    if ([System.IO.Path]::DirectorySeparatorChar -eq '\') {
        [System.StringComparison]::OrdinalIgnoreCase
    }
    else {
        [System.StringComparison]::Ordinal
    }
$platformKey = $null
$expectedPlatformTriple = $null
$verusDirectoryLeaf = $null
$verusExecutableLeaf = $null
$verusZ3Leaf = $null
$rustupExecutableLeaf = $null
$rustcExecutableLeaf = $null
$cargoExecutableLeaf = $null
$offlineBundleRootFull = $null
if ($NoReport -and $PSBoundParameters.ContainsKey("ReportPath")) {
    throw "-NoReport and -ReportPath cannot be used together"
}
if (-not $NoReport) {
    if ([string]::IsNullOrWhiteSpace($ReportPath)) {
        $ReportPath = Join-Path $resultsDir "verification-report.json"
    }
    elseif (-not [System.IO.Path]::IsPathRooted($ReportPath)) {
        $ReportPath = [System.IO.Path]::GetFullPath((Join-Path (Get-Location) $ReportPath))
    }
    else {
        $ReportPath = [System.IO.Path]::GetFullPath($ReportPath)
    }
}
$targets = @(
    [pscustomobject]@{
        Name = "M0"
        SourcePath = Join-Path $scriptDir "m0.rs"
        ExtraArguments = @()
        ContributionParent = "__full__"
    },
    [pscustomobject]@{
        Name = "R1"
        SourcePath = Join-Path $scriptDir "t1_replay.rs"
        ExtraArguments = @()
        ContributionParent = "__skip__"
    },
    [pscustomobject]@{
        Name = "B1"
        SourcePath = Join-Path $scriptDir "t1_append.rs"
        ExtraArguments = @()
        ContributionParent = "__skip__"
    },
    [pscustomobject]@{
        Name = "C1"
        SourcePath = Join-Path $scriptDir "t1_replay_append.rs"
        ExtraArguments = @()
        ContributionParent = "__full__"
    },
    [pscustomobject]@{
        Name = "D1"
        SourcePath = Join-Path $scriptDir "t1_durable_append.rs"
        ExtraArguments = @()
        ContributionParent = "C1"
    },
    [pscustomobject]@{
        Name = "Q1"
        SourcePath = Join-Path $scriptDir "t1_durable_queries.rs"
        ExtraArguments = @()
        ContributionParent = "C1"
    },
    [pscustomobject]@{
        Name = "K1"
        SourcePath = Join-Path $scriptDir "k1_executable_kernel.rs"
        ExtraArguments = @()
        ContributionParent = "Q1"
    },
    [pscustomobject]@{
        Name = "K2-G0"
        SourcePath = Join-Path $scriptDir "k2_executable_kernel_refinement.rs"
        ExtraArguments = @()
        ContributionParent = "K1"
    },
    [pscustomobject]@{
        Name = "K2-T0"
        SourcePath = Join-Path $scriptDir "k2_durable_record_kernel.rs"
        ExtraArguments = @()
        ContributionParent = "K2-G0"
    },
    [pscustomobject]@{
        Name = "K3-A0"
        SourcePath = Join-Path $scriptDir "k3_append_linearization_kernel.rs"
        ExtraArguments = @()
        ContributionParent = "K2-T0"
    },
    [pscustomobject]@{
        Name = "K4-C0"
        SourcePath = Join-Path $scriptDir "k4_manifest_config_refinement.rs"
        ExtraArguments = @()
        ContributionParent = "K3-A0"
    },
    [pscustomobject]@{
        Name = "K4-R0"
        SourcePath = Join-Path $scriptDir "k4_parameterized_authorize.rs"
        ExtraArguments = @()
        ContributionParent = "K4-C0"
    },
    [pscustomobject]@{
        Name = "K4-R1"
        SourcePath = Join-Path $scriptDir "k4_parameterized_prepare_start.rs"
        ExtraArguments = @()
        ContributionParent = "K4-R0"
    },
    [pscustomobject]@{
        Name = "K4-R2"
        SourcePath = Join-Path $scriptDir "k4_parameterized_authorize_mutation.rs"
        ExtraArguments = @()
        ContributionParent = "K4-R1"
    },
    [pscustomobject]@{
        Name = "K4-R3"
        SourcePath = Join-Path $scriptDir "k4_parameterized_prepare_mutation.rs"
        ExtraArguments = @()
        ContributionParent = "K4-R2"
    },
    [pscustomobject]@{
        Name = "K4-R4"
        SourcePath = Join-Path $scriptDir "k4_parameterized_arm.rs"
        ExtraArguments = @()
        ContributionParent = "K4-R3"
    },
    [pscustomobject]@{
        Name = "K4-R5"
        SourcePath = Join-Path $scriptDir "k4_parameterized_start_mutation.rs"
        ExtraArguments = @()
        ContributionParent = "K4-R4"
    },
    [pscustomobject]@{
        Name = "K4-R6"
        SourcePath = Join-Path $scriptDir "k4_parameterized_outcome_mutation.rs"
        ExtraArguments = @()
        ContributionParent = "K4-R5"
    },
    [pscustomobject]@{
        Name = "K4-R7"
        SourcePath = Join-Path $scriptDir "k4_parameterized_commit_mutation.rs"
        ExtraArguments = @()
        ContributionParent = "K4-R6"
    },
    [pscustomobject]@{
        Name = "K4-A0"
        SourcePath = Join-Path $scriptDir "k4_manifest_append_certificate.rs"
        ExtraArguments = @()
        ContributionParent = "K4-R7"
    },
    [pscustomobject]@{
        Name = "K4-A1"
        SourcePath = Join-Path $scriptDir "k4_manifest_append_state_bridge.rs"
        ExtraArguments = @()
        ContributionParent = "K4-A0"
    },
    [pscustomobject]@{
        Name = "K4-A2"
        SourcePath = Join-Path $scriptDir "k4_generic_append_state_bridge.rs"
        ExtraArguments = @()
        ContributionParent = "K4-A1"
    },
    [pscustomobject]@{
        Name = "K4-A3"
        SourcePath = Join-Path $scriptDir "k4_terminal_recovery_bridge.rs"
        ExtraArguments = @()
        ContributionParent = "K4-A2"
    },
    [pscustomobject]@{
        Name = "K4-A4"
        SourcePath = Join-Path $scriptDir "k4_crash_recovery_control.rs"
        ExtraArguments = @()
        ContributionParent = "K4-A3"
    },
    [pscustomobject]@{
        Name = "B2-R"
        SourcePath = Join-Path $scriptDir "t1_broker_records.rs"
        ExtraArguments = @()
        ContributionParent = "Q1"
    },
    [pscustomobject]@{
        Name = "B2-C"
        SourcePath = Join-Path $scriptDir "t1_full_config.rs"
        ExtraArguments = @()
        ContributionParent = "B2-R"
    },
    [pscustomobject]@{
        Name = "B2-P0"
        SourcePath = Join-Path $scriptDir "t1_broker_physical.rs"
        ExtraArguments = @()
        ContributionParent = "B2-C"
    },
    [pscustomobject]@{
        Name = "B2-P1"
        SourcePath = Join-Path $scriptDir "t1_broker_physical_causality.rs"
        ExtraArguments = @()
        ContributionParent = "B2-P0"
    },
    [pscustomobject]@{
        Name = "B2-P2"
        SourcePath = Join-Path $scriptDir "t1_broker_physical_refinement.rs"
        ExtraArguments = @()
        ContributionParent = "B2-P1"
    },
    [pscustomobject]@{
        Name = "B2-P3"
        SourcePath = Join-Path $scriptDir "t1_broker_terminal_provenance.rs"
        ExtraArguments = @()
        ContributionParent = "B2-P2"
    },
    [pscustomobject]@{
        Name = "B2-L"
        SourcePath = Join-Path $scriptDir "t1_broker_contract.rs"
        ExtraArguments = @()
        ContributionParent = "B2-P3"
    },
    [pscustomobject]@{
        Name = "B2-A"
        SourcePath = Join-Path $scriptDir "t1_broker_append_bridge.rs"
        ExtraArguments = @()
        ContributionParent = "B2-L"
    },
    [pscustomobject]@{
        Name = "G0"
        SourcePath = Join-Path $scriptDir "t1_global_event.rs"
        ExtraArguments = @()
        ContributionParent = "B2-A"
    },
    [pscustomobject]@{
        Name = "G1-P"
        SourcePath = Join-Path $scriptDir "t1_global_projections.rs"
        ExtraArguments = @()
        ContributionParent = "G0"
    },
    [pscustomobject]@{
        Name = "G1-E"
        SourcePath = Join-Path $scriptDir "t1_broker_execution.rs"
        ExtraArguments = @()
        ContributionParent = "G1-P"
    },
    [pscustomobject]@{
        Name = "T1"
        SourcePath = Join-Path $scriptDir "t1_parameterized_broker_safety.rs"
        ExtraArguments = @()
        ContributionParent = "G1-E"
    },
    [pscustomobject]@{
        Name = "T2-J0"
        SourcePath = Join-Path $scriptDir "t2_atomic_runtime.rs"
        ExtraArguments = @()
        ContributionParent = "T1"
    },
    [pscustomobject]@{
        Name = "T2-J1"
        SourcePath = Join-Path $scriptDir "t2_atomic_trace.rs"
        ExtraArguments = @()
        ContributionParent = "T2-J0"
    },
    [pscustomobject]@{
        Name = "T2-E"
        SourcePath = Join-Path $scriptDir "t2_event_projection.rs"
        ExtraArguments = @()
        ContributionParent = "T2-J1"
    },
    [pscustomobject]@{
        Name = "T2-R"
        SourcePath = Join-Path $scriptDir "t2_representation.rs"
        ExtraArguments = @()
        ContributionParent = "T2-E"
    },
    [pscustomobject]@{
        Name = "T2"
        SourcePath = Join-Path $scriptDir "t2_atomic_journal_simulation.rs"
        ExtraArguments = @()
        ContributionParent = "T2-R"
    },
    [pscustomobject]@{
        Name = "T3-W0"
        SourcePath = Join-Path $scriptDir "t3_wal_runtime.rs"
        ExtraArguments = @()
        ContributionParent = "T2"
    },
    [pscustomobject]@{
        Name = "T3-W1-T"
        SourcePath = Join-Path $scriptDir "t3_wal_trace.rs"
        ExtraArguments = @()
        ContributionParent = "T3-W0"
    },
    [pscustomobject]@{
        Name = "T3-W1-E"
        SourcePath = Join-Path $scriptDir "t3_wal_event_projection.rs"
        ExtraArguments = @()
        ContributionParent = "T3-W1-T"
    },
    [pscustomobject]@{
        Name = "T3-W1-R"
        SourcePath = Join-Path $scriptDir "t3_wal_representation.rs"
        ExtraArguments = @()
        ContributionParent = "T3-W1-E"
    },
    [pscustomobject]@{
        Name = "T3"
        SourcePath = Join-Path $scriptDir "t3_wal_journal_simulation.rs"
        ExtraArguments = @()
        ContributionParent = "T3-W1-R"
    },
    [pscustomobject]@{
        Name = "T4-C0"
        SourcePath = Join-Path $scriptDir "t4_closed_composition.rs"
        ExtraArguments = @()
        ContributionParent = "T3"
    },
    [pscustomobject]@{
        Name = "T4-C1"
        SourcePath = Join-Path $scriptDir "t4_context_interface.rs"
        ExtraArguments = @()
        ContributionParent = "T4-C0"
    },
    [pscustomobject]@{
        Name = "T4-C2"
        SourcePath = Join-Path $scriptDir "t4_contextual_composition.rs"
        ExtraArguments = @()
        ContributionParent = "T4-C1"
    },
    [pscustomobject]@{
        Name = "T5-S0"
        SourcePath = Join-Path $scriptDir "t5_commit_step.rs"
        ExtraArguments = @()
        ContributionParent = "T4-C2"
    },
    [pscustomobject]@{
        Name = "T5-E0"
        SourcePath = Join-Path $scriptDir "t5_commit_execution.rs"
        ExtraArguments = @()
        ContributionParent = "T5-S0"
    },
    [pscustomobject]@{
        Name = "T5-R0"
        SourcePath = Join-Path $scriptDir "t5_commit_recovery.rs"
        ExtraArguments = @()
        ContributionParent = "T5-E0"
    },
    [pscustomobject]@{
        Name = "T5-R1"
        SourcePath = Join-Path $scriptDir "t5_durable_success_recovery.rs"
        ExtraArguments = @()
        ContributionParent = "T5-R0"
    },
    [pscustomobject]@{
        Name = "T5-C0"
        SourcePath = Join-Path $scriptDir "t5_commit_contextual.rs"
        ExtraArguments = @()
        ContributionParent = "T5-R1"
    },
    [pscustomobject]@{
        Name = "H1"
        SourcePath = Join-Path $scriptDir "h1_artifact_nonvacuity.rs"
        ExtraArguments = @()
        ContributionParent = "T5-C0"
    },
    [pscustomobject]@{
        Name = "T6-D0"
        SourcePath = Join-Path $scriptDir "t6_terminal_definitions.rs"
        ExtraArguments = @()
        ContributionParent = "T5-C0"
    },
    [pscustomobject]@{
        Name = "T6-E0"
        SourcePath = Join-Path $scriptDir "t6_terminal_evidence.rs"
        ExtraArguments = @()
        ContributionParent = "T6-D0"
    },
    [pscustomobject]@{
        Name = "T6-C0"
        SourcePath = Join-Path $scriptDir "t6_terminal_compatibility.rs"
        ExtraArguments = @()
        ContributionParent = "T6-E0"
    },
    [pscustomobject]@{
        Name = "T6-S0"
        SourcePath = Join-Path $scriptDir "t6_terminal_bridge.rs"
        ExtraArguments = @()
        ContributionParent = "T6-C0"
    },
    [pscustomobject]@{
        Name = "T6-A0"
        SourcePath = Join-Path $scriptDir "t6_adapter_semantic_closure.rs"
        ExtraArguments = @()
        ContributionParent = "T6-S0"
    },
    [pscustomobject]@{
        Name = "T6-A1"
        SourcePath = Join-Path $scriptDir "t6_adapter_executable_refinement.rs"
        ExtraArguments = @()
        ContributionParent = "T6-A0"
    },
    [pscustomobject]@{
        Name = "H2"
        SourcePath = Join-Path $scriptDir "h2_durable_success_recovery_witness.rs"
        ExtraArguments = @()
        ContributionParent = "T6-A0"
    },
    [pscustomobject]@{
        Name = "T6-M0"
        SourcePath = Join-Path $scriptDir "t6_mediation_exclusivity.rs"
        ExtraArguments = @()
        ContributionParent = "T6-A1"
    },
    [pscustomobject]@{
        Name = "T6-P0"
        SourcePath = Join-Path $scriptDir "t6_prefix_simulation.rs"
        ExtraArguments = @()
        ContributionParent = "T6-M0"
    },
    [pscustomobject]@{
        Name = "T6-X0"
        SourcePath = Join-Path $scriptDir "t6_contextual_end_to_end.rs"
        ExtraArguments = @()
        ContributionParent = "T6-P0"
    },
    [pscustomobject]@{
        Name = "T6-RO0"
        SourcePath = Join-Path $scriptDir "t6_readonly_operational.rs"
        ExtraArguments = @()
        ContributionParent = "T6-X0"
    },
    [pscustomobject]@{
        Name = "T6-DD0"
        SourcePath = Join-Path $scriptDir "t6_deduplicated_operational.rs"
        ExtraArguments = @()
        ContributionParent = "T6-RO0"
    },
    [pscustomobject]@{
        Name = "T6-DD1"
        SourcePath = Join-Path $scriptDir "t6_deduplicated_invariant.rs"
        ExtraArguments = @()
        ContributionParent = "T6-DD0"
    },
    [pscustomobject]@{
        Name = "T6-DD2"
        SourcePath = Join-Path $scriptDir "t6_deduplicated_witness.rs"
        ExtraArguments = @()
        ContributionParent = "T6-DD1"
    },
    [pscustomobject]@{
        Name = "T6-DD3"
        SourcePath = Join-Path $scriptDir "t6_deduplicated_mediation.rs"
        ExtraArguments = @()
        ContributionParent = "T6-DD2"
    },
    [pscustomobject]@{
        Name = "T6-DD4"
        SourcePath = Join-Path $scriptDir "t6_deduplicated_contextual.rs"
        ExtraArguments = @()
        ContributionParent = "T6-DD3"
    },
    [pscustomobject]@{
        Name = "T6-DD5"
        SourcePath = Join-Path $scriptDir "t6_deduplicated_request_family.rs"
        ExtraArguments = @()
        ContributionParent = "T6-DD4"
    }
)

function Get-Sha256Lower {
    param([Parameter(Mandatory = $true)][string]$Path)

    (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
}

function Get-PathKey {
    param([Parameter(Mandatory = $true)][string]$Path)

    $fullPath = [System.IO.Path]::GetFullPath($Path)
    if ($script:PathComparison -eq
        [System.StringComparison]::OrdinalIgnoreCase) {
        return $fullPath.ToLowerInvariant()
    }
    $fullPath
}

function Assert-SafeLeafName {
    param(
        [Parameter(Mandatory = $true)][string]$Name,
        [Parameter(Mandatory = $true)][string]$Description
    )

    if ([string]::IsNullOrWhiteSpace($Name) -or
        [System.IO.Path]::IsPathRooted($Name) -or
        [System.IO.Path]::GetFileName($Name) -ne $Name -or
        $Name -eq "." -or $Name -eq ".." -or
        $Name -notmatch '^[A-Za-z0-9][A-Za-z0-9._-]*$') {
        throw "$Description must be a safe leaf name: $Name"
    }
    $Name
}

function Assert-PathWithinRoot {
    param(
        [Parameter(Mandatory = $true)][string]$Root,
        [Parameter(Mandatory = $true)][string]$Path,
        [switch]$AllowRoot
    )

    $fullRoot = [System.IO.Path]::GetFullPath($Root).TrimEnd(
        [System.IO.Path]::DirectorySeparatorChar,
        [System.IO.Path]::AltDirectorySeparatorChar)
    $fullPath = [System.IO.Path]::GetFullPath($Path)
    $prefix = $fullRoot + [System.IO.Path]::DirectorySeparatorChar
    $isRoot = $fullPath.Equals(
        $fullRoot,
        $script:PathComparison)
    if ((-not $AllowRoot -or -not $isRoot) -and
        -not $fullPath.StartsWith(
            $prefix,
            $script:PathComparison)) {
        throw "Path must remain below $fullRoot`: $fullPath"
    }
    $fullPath
}

function Get-DeterministicTreeMetadata {
    param([Parameter(Mandatory = $true)][string]$Root)

    $fullRoot = [System.IO.Path]::GetFullPath($Root).TrimEnd(
        [System.IO.Path]::DirectorySeparatorChar,
        [System.IO.Path]::AltDirectorySeparatorChar)
    if (-not (Test-Path -LiteralPath $fullRoot -PathType Container)) {
        throw "Tree root is missing: $fullRoot"
    }
    $items = @(Get-ChildItem -LiteralPath $fullRoot -Recurse -Force)
    foreach ($item in $items) {
        if (($item.Attributes -band [System.IO.FileAttributes]::ReparsePoint) -ne 0) {
            throw "Tree hashing does not admit reparse points: $($item.FullName)"
        }
    }
    [string[]]$relativePaths = @($items | ForEach-Object {
        $_.FullName.Substring($fullRoot.Length + 1).Replace('\', '/')
    })
    [System.Array]::Sort(
        $relativePaths,
        [System.StringComparer]::Ordinal)
    $manifest = New-Object System.Text.StringBuilder
    foreach ($relativePath in $relativePaths) {
        $fullPath = Join-Path $fullRoot $relativePath.Replace(
            '/',
            [System.IO.Path]::DirectorySeparatorChar)
        $item = Get-Item -Force -LiteralPath $fullPath
        if ($item.PSIsContainer) {
            [void]$manifest.Append("D:")
            [void]$manifest.Append($relativePath.Length)
            [void]$manifest.Append(":")
            [void]$manifest.Append($relativePath)
            [void]$manifest.Append("`n")
            continue
        }
        $hash = Get-Sha256Lower -Path $fullPath
        [void]$manifest.Append("F:")
        [void]$manifest.Append($relativePath.Length)
        [void]$manifest.Append(":")
        [void]$manifest.Append($relativePath)
        [void]$manifest.Append(":")
        [void]$manifest.Append($item.Length)
        [void]$manifest.Append(":")
        [void]$manifest.Append($hash)
        [void]$manifest.Append("`n")
    }
    $sha = [System.Security.Cryptography.SHA256]::Create()
    try {
        $bytes = [System.Text.Encoding]::UTF8.GetBytes($manifest.ToString())
        $digest = $sha.ComputeHash($bytes)
    }
    finally {
        $sha.Dispose()
    }
    [pscustomobject]@{
        FileCount = @($items | Where-Object { -not $_.PSIsContainer }).Count
        Sha256 = ([System.BitConverter]::ToString($digest) -replace '-', '').ToLowerInvariant()
    }
}

function Get-DirectPathImports {
    param([Parameter(Mandatory = $true)][string]$SourcePath)

    $sourceText = Get-Content -Raw -LiteralPath $SourcePath
    $sourceDirectory = Split-Path -Parent $SourcePath
    if ($sourceText -match '/\*|\*/') {
        throw "Block comments are not admitted by the simple module grammar in $SourcePath"
    }
    if ($sourceText -match '\binclude(?:_str|_bytes)?\s*//' -or
        $sourceText -match '\bmod\s*//') {
        throw "Comment-interposed module loading is not admitted in $SourcePath"
    }
    if ($sourceText -match '\binclude(?:_str|_bytes)?\s*!') {
        throw "Unsupported include-style module loading in $SourcePath"
    }
    if ($sourceText -match '(?im)^\s*(?:pub\s+)?use\b[^;]*?\binclude(?:_str|_bytes)?\b') {
        throw "Aliasing include-style macros is not admitted in $SourcePath"
    }
    $pathOccurrenceCount = [regex]::Matches(
        $sourceText,
        '(?is)#\s*\[\s*path\b').Count
    $moduleOccurrenceCount = [regex]::Matches(
        $sourceText,
        '(?is)\b(?:pub\s+)?mod\s+[A-Za-z_][A-Za-z0-9_]*\s*;').Count
    $lines = @($sourceText -split "`r?`n")
    $imports = @()
    $pathLineCount = 0
    $moduleLineCount = 0
    $pathQualifiedModuleLines = @{}
    for ($lineIndex = 0; $lineIndex -lt $lines.Count; $lineIndex++) {
        $line = $lines[$lineIndex]
        if ($line -match '^\s*#\s*\[\s*path\s*=\s*"([^"\r\n]+)"\s*\]\s*$') {
            $pathLineCount++
            $declaredPath = Assert-SafeLeafName `
                -Name $matches[1] `
                -Description "Rust #[path] value"
            if ([System.IO.Path]::GetExtension($declaredPath) -ne ".rs") {
                throw "Rust #[path] must name a .rs source: $declaredPath"
            }
            $moduleLine = $lineIndex + 1
            if ($moduleLine -ge $lines.Count -or
                $lines[$moduleLine] -notmatch '^\s*(?:pub\s+)?mod\s+[A-Za-z_][A-Za-z0-9_]*\s*;\s*$') {
                throw ("Rust #[path] must be followed immediately by one simple " +
                    "module declaration in $SourcePath")
            }
            $pathQualifiedModuleLines[$moduleLine] = $true
            $imports += [pscustomobject]@{
                DeclaredPath = $declaredPath
                FullPath = [System.IO.Path]::GetFullPath(
                    (Join-Path $sourceDirectory $declaredPath))
            }
        }
        elseif ($line -match '#\s*\[\s*path\b') {
            throw "Unsupported multiline or noncanonical #[path] form in $SourcePath"
        }

        if ($line -match '^\s*(?:pub\s+)?mod\s+[A-Za-z_][A-Za-z0-9_]*\s*;\s*$') {
            $moduleLineCount++
            if (-not $pathQualifiedModuleLines.ContainsKey($lineIndex)) {
                throw "Implicit Rust module loading is not admitted in $SourcePath"
            }
        }
    }
    if ($pathOccurrenceCount -ne $pathLineCount -or
        $moduleOccurrenceCount -ne $moduleLineCount) {
        throw "Unsupported multiline module-loading grammar in $SourcePath"
    }
    $imports
}

function Write-VerificationReport {
    param(
        [Parameter(Mandatory = $true)][object]$Report,
        [Parameter(Mandatory = $true)][string]$Destination
    )

    $fullDestination = [System.IO.Path]::GetFullPath($Destination)
    $destinationDirectory = Split-Path -Parent $fullDestination
    New-Item -ItemType Directory -Force -Path $destinationDirectory | Out-Null
    $partial = $fullDestination + ".partial-" + [guid]::NewGuid().ToString("N")
    try {
        $json = $Report | ConvertTo-Json -Depth 20
        $utf8WithoutBom = New-Object System.Text.UTF8Encoding($false)
        [System.IO.File]::WriteAllText(
            $partial,
            $json + [System.Environment]::NewLine,
            $utf8WithoutBom)
        Move-Item -Force -LiteralPath $partial -Destination $fullDestination
    }
    finally {
        Remove-Item -Force -LiteralPath $partial -ErrorAction SilentlyContinue
    }
}

function Assert-RegisteredSourceHashes {
    param(
        [Parameter(Mandatory = $true)][object[]]$RegisteredTargets,
        [Parameter(Mandatory = $true)][hashtable]$ReportsByName
    )

    foreach ($registeredTarget in $RegisteredTargets) {
        $expectedHash = $ReportsByName[$registeredTarget.Name].source_sha256
        $actualHash = Get-Sha256Lower -Path $registeredTarget.SourcePath
        if ($actualHash -ne $expectedHash) {
            throw ("Registered source changed during verification: " +
                $registeredTarget.SourcePath)
        }
    }
}

function Assert-HashedFileIntegrity {
    param(
        [Parameter(Mandatory = $true)][object[]]$Inputs,
        [Parameter(Mandatory = $true)][string]$Description
    )

    foreach ($input in $Inputs) {
        $path = [string]$input.path
        if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
            throw "$Description disappeared during verification: $path"
        }
        if ((Get-Sha256Lower -Path $path) -ne [string]$input.sha256) {
            throw "$Description changed during verification: $path"
        }
    }
}

function Assert-SourceSnapshot {
    param(
        [Parameter(Mandatory = $true)][string]$SnapshotRoot,
        [Parameter(Mandatory = $true)][object[]]$RegisteredTargets,
        [Parameter(Mandatory = $true)][hashtable]$ReportsByName,
        [Parameter(Mandatory = $true)][hashtable]$SnapshotPathsByName,
        [string]$ExpectedTreeSha256 = ""
    )

    $fullSnapshotRoot = [System.IO.Path]::GetFullPath($SnapshotRoot)
    $children = @(Get-ChildItem -LiteralPath $fullSnapshotRoot -Force)
    if (@($children | Where-Object { $_.PSIsContainer }).Count -ne 0) {
        throw "The source snapshot must use a flat files-only layout"
    }
    [string[]]$expectedNames = @($RegisteredTargets | ForEach-Object {
        [System.IO.Path]::GetFileName($_.SourcePath).ToLowerInvariant()
    })
    [string[]]$actualNames = @($children | ForEach-Object {
        $_.Name.ToLowerInvariant()
    })
    [System.Array]::Sort($expectedNames, [System.StringComparer]::Ordinal)
    [System.Array]::Sort($actualNames, [System.StringComparer]::Ordinal)
    if ($expectedNames.Count -ne $RegisteredTargets.Count -or
        $actualNames.Count -ne $RegisteredTargets.Count -or
        @(Compare-Object -ReferenceObject $expectedNames `
            -DifferenceObject $actualNames -CaseSensitive).Count -ne 0) {
        throw "The source snapshot membership does not exactly match the registry"
    }

    foreach ($registeredTarget in $RegisteredTargets) {
        $snapshotPath = Assert-PathWithinRoot `
            -Root $fullSnapshotRoot `
            -Path $SnapshotPathsByName[$registeredTarget.Name]
        if (-not (Test-Path -LiteralPath $snapshotPath -PathType Leaf)) {
            throw "Snapshot source is missing for $($registeredTarget.Name)"
        }
        $expectedHash = $ReportsByName[$registeredTarget.Name].source_sha256
        if ((Get-Sha256Lower -Path $snapshotPath) -ne $expectedHash) {
            throw "Snapshot source hash changed for $($registeredTarget.Name)"
        }
        $attributes = (Get-Item -Force -LiteralPath $snapshotPath).Attributes
        if (($attributes -band [System.IO.FileAttributes]::ReadOnly) -eq 0) {
            throw "Snapshot source is not read-only: $snapshotPath"
        }
    }
    $metadata = Get-DeterministicTreeMetadata -Root $fullSnapshotRoot
    if (-not [string]::IsNullOrWhiteSpace($ExpectedTreeSha256) -and
        $metadata.Sha256 -ne $ExpectedTreeSha256) {
        throw "The source snapshot tree changed during verification"
    }
    $metadata
}

function Assert-TreeHash {
    param(
        [Parameter(Mandatory = $true)][string]$Root,
        [Parameter(Mandatory = $true)][string]$ExpectedSha256,
        [Parameter(Mandatory = $true)][string]$Description
    )

    $metadata = Get-DeterministicTreeMetadata -Root $Root
    if ($metadata.Sha256 -ne $ExpectedSha256) {
        throw "$Description changed during verification"
    }
    $metadata
}

function Remove-FreshRunRoot {
    param([Parameter(Mandatory = $true)][string]$RunRoot)

    if (-not (Test-Path -LiteralPath $RunRoot)) {
        return
    }
    $items = @(Get-ChildItem -LiteralPath $RunRoot -Recurse -Force -ErrorAction SilentlyContinue)
    foreach ($item in $items) {
        if (-not $item.PSIsContainer -and
            ($item.Attributes -band [System.IO.FileAttributes]::ReadOnly) -ne 0) {
            $item.Attributes = $item.Attributes -band (-bnot [System.IO.FileAttributes]::ReadOnly)
        }
    }
    Remove-Item -Recurse -Force -LiteralPath $RunRoot
}

function Assert-PassedReportSemanticConsistency {
    param([Parameter(Mandatory = $true)][object]$Report)

    if ($Report.status -ne "passed") {
        throw "Semantic consistency is defined here only for passed reports"
    }
    $entries = @($Report.targets)
    $count = $entries.Count
    if ($count -ne [int]$Report.summary.registered_target_count -or
        $count -ne [int]$Report.summary.registered_source_count -or
        $count -ne [int]$Report.summary.present_source_count -or
        $count -ne [int]$Report.summary.verified_target_count -or
        $count -ne [int]$Report.source_snapshot.source_file_count) {
        throw "Passed-report target and source counts are inconsistent"
    }
    $names = @($entries | ForEach-Object { $_.name } | Sort-Object -Unique)
    $sourcePaths = @($entries | ForEach-Object { $_.source_path } | Sort-Object -Unique)
    $snapshotPaths = @($entries | ForEach-Object {
        $_.snapshot_source_path
    } | Sort-Object -Unique)
    if ($names.Count -ne $count -or $sourcePaths.Count -ne $count -or
        $snapshotPaths.Count -ne $count) {
        throw "Passed-report target names and source paths must be unique"
    }
    if (-not $Report.source_snapshot.exact_membership_validated -or
        -not $Report.source_snapshot.source_hashes_match_registry -or
        -not $Report.source_snapshot.all_files_read_only -or
        [int]$Report.source_snapshot.pre_target_validation_count -ne $count -or
        [int]$Report.source_snapshot.post_target_validation_count -ne $count -or
        -not $Report.source_snapshot.final_validation_passed -or
        -not $Report.source_snapshot.removed_after_run) {
        throw "Passed-report source snapshot evidence is incomplete"
    }
    if (-not $Report.toolchain.observed.fresh_rust_environment -or
        -not $Report.toolchain.observed.rust_toolchain_tree_unchanged -or
        -not $Report.toolchain.observed.verus_tree_unchanged) {
        throw "Passed-report verifier toolchain isolation evidence is incomplete"
    }

    $expectedArguments = @("--crate-type", "lib", "--no-cheating")
    $byName = @{}
    $sum = 0
    $runningNonDuplicated = 0
    $parentDeltaCount = 0
    foreach ($entry in $entries) {
        if ($entry.status -ne "passed" -or
            [int]$entry.verus_exit_code -ne 0 -or
            [int]$entry.verus_errors -ne 0) {
            throw "Passed report contains a target that did not pass: $($entry.name)"
        }
        $arguments = @($entry.verus_arguments)
        if ($arguments.Count -ne $expectedArguments.Count) {
            throw "Unexpected Verus argument count for $($entry.name)"
        }
        for ($argumentIndex = 0; $argumentIndex -lt $expectedArguments.Count; $argumentIndex++) {
            if ($arguments[$argumentIndex] -ne $expectedArguments[$argumentIndex]) {
                throw "Unexpected Verus arguments for $($entry.name)"
            }
        }

        $verified = [int]$entry.verified_obligations_total
        $delta = [int]$entry.contribution_delta
        if ($entry.contribution_mode -eq "full") {
            if ($delta -ne $verified) {
                throw "Full target delta is inconsistent for $($entry.name)"
            }
        }
        elseif ($entry.contribution_mode -eq "excluded") {
            if ($delta -ne 0) {
                throw "Excluded target contributes a nonzero delta: $($entry.name)"
            }
        }
        elseif ($entry.contribution_mode -eq "parent_delta") {
            $parentDeltaCount++
            if (-not $byName.ContainsKey($entry.contribution_parent)) {
                throw "Target parent is missing or not earlier: $($entry.name)"
            }
            $expectedDelta = $verified - [int]$byName[$entry.contribution_parent].verified_obligations_total
            if ($expectedDelta -lt 0 -or $delta -ne $expectedDelta -or
                -not $entry.immediate_parent_import_validated -or
                @($entry.direct_path_imports).Count -ne 1) {
                throw "Parent-delta semantics are inconsistent for $($entry.name)"
            }
        }
        else {
            throw "Unknown contribution mode for $($entry.name)"
        }
        $sum += $verified
        $runningNonDuplicated += $delta
        if ([int]$entry.non_duplicated_total_after -ne $runningNonDuplicated) {
            throw "Running non-duplicated total is inconsistent for $($entry.name)"
        }
        $byName[$entry.name] = $entry
    }
    if ($sum -ne [int]$Report.summary.sum_of_target_obligations -or
        $runningNonDuplicated -ne
            [int]$Report.summary.non_duplicated_verified_obligations -or
        $parentDeltaCount -ne
            [int]$Report.policy.cumulative_parent_imports_validated) {
        throw "Passed-report summary arithmetic is inconsistent"
    }
}

function Get-CanonicalVersionLine {
    param(
        [Parameter(Mandatory = $true)][string]$Text,
        [Parameter(Mandatory = $true)][string]$Pattern,
        [Parameter(Mandatory = $true)][string]$ToolName
    )

    $matchingLines = @($Text -split "`r?`n" | Where-Object {
        $_ -match $Pattern
    })
    if ($matchingLines.Count -ne 1) {
        throw ("Could not isolate exactly one canonical $ToolName version line: " +
            $Text)
    }
    $matchingLines[0].Trim()
}

$runStarted = [System.DateTimeOffset]::UtcNow
$runId = [guid]::NewGuid().ToString("N")
$runRoot = $null
$sourceSnapshotRoot = $null
$snapshotSourceByName = @{}
$schemaHash = if (Test-Path -LiteralPath $schemaPath) {
    Get-Sha256Lower -Path $schemaPath
}
else {
    $null
}
$driverHash = Get-Sha256Lower -Path $MyInvocation.MyCommand.Path
$forbiddenProofPattern = '\b(assume|admit|external_body|external_fn_specification|assume_specification|axiom|get_Some|recommends|rlimit|resource_limit|spinoff|spinoff_prover)\b|verifier\s*::\s*external|verifier\s*\('
$forbiddenArgumentPattern = '(?s).+'
$targetReports = @()
foreach ($target in $targets) {
    $sourceHash = $null
    if (Test-Path -LiteralPath $target.SourcePath) {
        try {
            $sourceHash = Get-Sha256Lower -Path $target.SourcePath
        }
        catch {
            $sourceHash = $null
        }
    }
    $contributionMode = if ($target.ContributionParent -eq "__full__") {
        "full"
    }
    elseif ($target.ContributionParent -eq "__skip__") {
        "excluded"
    }
    else {
        "parent_delta"
    }
    $contributionParent = if ($contributionMode -eq "parent_delta") {
        $target.ContributionParent
    }
    else {
        $null
    }
    $targetReports += [pscustomobject][ordered]@{
        name = $target.Name
        source_path = "mechanized/" + [System.IO.Path]::GetFileName($target.SourcePath)
        source_sha256 = $sourceHash
        snapshot_source_path = "sources/" + [System.IO.Path]::GetFileName($target.SourcePath)
        direct_path_imports = @()
        contribution_mode = $contributionMode
        contribution_parent = $contributionParent
        immediate_parent_import_validated = if ($contributionMode -eq "parent_delta") { $false } else { $null }
        verus_arguments = @("--crate-type", "lib", "--no-cheating") + @($target.ExtraArguments)
        status = "pending"
        started_at_utc = $null
        completed_at_utc = $null
        duration_ms = $null
        verified_obligations_total = $null
        verus_errors = $null
        verus_exit_code = $null
        contribution_delta = $null
        non_duplicated_total_after = $null
        error = $null
    }
}

$lockHash = if (Test-Path -LiteralPath $lockPath) {
    Get-Sha256Lower -Path $lockPath
}
else {
    $null
}
$report = [pscustomobject][ordered]@{
    schema = "vetra.verus-verification-report"
    schema_version = 1
    schema_path = "mechanized/results/verification-report.schema.v1.json"
    schema_sha256 = $schemaHash
    status = "running"
    started_at_utc = $runStarted.ToString("o")
    completed_at_utc = $null
    duration_ms = $null
    error = $null
    environment = [pscustomobject][ordered]@{
        os_description = [System.Runtime.InteropServices.RuntimeInformation]::OSDescription
        os_architecture = [System.Runtime.InteropServices.RuntimeInformation]::OSArchitecture.ToString()
        process_architecture = [System.Runtime.InteropServices.RuntimeInformation]::ProcessArchitecture.ToString()
        powershell_version = $PSVersionTable.PSVersion.ToString()
    }
    policy = [pscustomobject][ordered]@{
        status = "pending"
        no_cheating = $true
        source_scan_is_case_insensitive = $true
        forbidden_source_pattern = $forbiddenProofPattern
        forbidden_extra_argument_pattern = $forbiddenArgumentPattern
        nonempty_extra_arguments_rejected = $false
        simple_path_module_grammar_enforced = $false
        complete_registered_source_coverage = $false
        all_direct_path_imports_registered = $false
        cumulative_parent_imports_validated = 0
    }
    source_snapshot = [pscustomobject][ordered]@{
        kind = "isolated-read-only-copy"
        run_id = $runId
        created_at_utc = $null
        source_file_count = $null
        manifest_sha256 = $null
        exact_membership_validated = $false
        source_hashes_match_registry = $false
        all_files_read_only = $false
        pre_target_validation_count = 0
        post_target_validation_count = 0
        final_validation_passed = $false
        removed_after_run = $false
    }
    toolchain = [pscustomobject][ordered]@{
        lock_path = "mechanized/toolchain.lock.json"
        lock_sha256 = $lockHash
        verification_driver_path = "mechanized/verify.ps1"
        verification_driver_sha256 = $driverHash
        declared = $null
        observed = [pscustomobject][ordered]@{
            verus_archive_sha256 = $null
            verus_executable_sha256 = $null
            verus_tree_sha256 = $null
            verus_tree_file_count = $null
            verus_tree_unchanged = $false
            verus_version = $null
            rustup_archive_sha256 = $null
            rustup_executable_sha256 = $null
            rustup_version = $null
            rustc_executable_sha256 = $null
            rustc_version = $null
            cargo_executable_sha256 = $null
            rust_toolchain_tree_sha256 = $null
            rust_toolchain_file_count = $null
            rust_toolchain_tree_unchanged = $false
            fresh_rust_environment = $false
            rustup_dist_server = $null
            rustup_update_root = $null
        }
    }
    summary = [pscustomobject][ordered]@{
        registered_target_count = $targets.Count
        registered_source_count = $targets.Count
        present_source_count = $null
        verified_target_count = 0
        sum_of_target_obligations = 0
        non_duplicated_verified_obligations = 0
    }
    targets = $targetReports
}
$targetReportByName = @{}
$nonDuplicatedVerified = 0
$sumOfTargetObligations = 0
$verifiedTargetCount = 0

try {
    if ($null -eq $report.schema_sha256) {
        throw "The verification-report schema is missing: $schemaPath"
    }
    if (-not [System.Environment]::Is64BitOperatingSystem -or
        -not [System.Environment]::Is64BitProcess -or
        [System.Runtime.InteropServices.RuntimeInformation]::OSArchitecture -ne
            [System.Runtime.InteropServices.Architecture]::X64) {
        throw "The verified core requires a 64-bit x86-64 operating system and process"
    }
    if ([System.Runtime.InteropServices.RuntimeInformation]::IsOSPlatform(
            [System.Runtime.InteropServices.OSPlatform]::Windows)) {
        $platformKey = "windows-x64"
        $expectedPlatformTriple = "x86_64-pc-windows-msvc"
        $verusDirectoryLeaf = "verus-x86-win"
        $verusExecutableLeaf = "verus.exe"
        $verusZ3Leaf = "z3.exe"
        $rustupExecutableLeaf = "rustup.exe"
        $rustcExecutableLeaf = "rustc.exe"
        $cargoExecutableLeaf = "cargo.exe"
    }
    elseif ([System.Runtime.InteropServices.RuntimeInformation]::IsOSPlatform(
            [System.Runtime.InteropServices.OSPlatform]::Linux)) {
        $platformKey = "linux-x64"
        $expectedPlatformTriple = "x86_64-unknown-linux-gnu"
        $verusDirectoryLeaf = "verus-x86-linux"
        $verusExecutableLeaf = "verus"
        $verusZ3Leaf = "z3"
        $rustupExecutableLeaf = "rustup"
        $rustcExecutableLeaf = "rustc"
        $cargoExecutableLeaf = "cargo"
    }
    else {
        throw "The verified core supports only 64-bit Windows and Linux on x86-64"
    }

# Fail closed when a new mechanized crate is added without being registered.
$declaredSources = @($targets | ForEach-Object {
    Get-PathKey -Path $_.SourcePath
} | Sort-Object -Unique)
$presentSources = @(Get-ChildItem -LiteralPath $scriptDir -Filter "*.rs" -File |
    ForEach-Object { Get-PathKey -Path $_.FullName } | Sort-Object -Unique)
if ($declaredSources.Count -ne $targets.Count) {
    throw "The verifier target list contains a duplicate source path"
}
$sourceCoverageDifference = @(
    Compare-Object -ReferenceObject $presentSources `
        -DifferenceObject $declaredSources
)
if ($sourceCoverageDifference.Count -ne 0) {
    $details = ($sourceCoverageDifference | ForEach-Object {
        "$($_.SideIndicator) $($_.InputObject)"
    }) -join "; "
    throw "Every mechanized .rs file must be an explicit verifier target: $details"
}

    $report.summary.present_source_count = $presentSources.Count
    $report.policy.complete_registered_source_coverage = $true
    $declaredNames = @($targets | ForEach-Object { $_.Name } | Sort-Object -Unique)
    if ($declaredNames.Count -ne $targets.Count) {
        throw "The verifier target list contains a duplicate target name"
    }
    for ($targetIndex = 0; $targetIndex -lt $targets.Count; $targetIndex++) {
        $target = $targets[$targetIndex]
        $targetReport = $targetReports[$targetIndex]
        $targetReportByName[$target.Name] = $targetReport
        if ($null -eq $targetReport.source_sha256) {
            throw "$($target.Name) source could not be hashed: $($target.SourcePath)"
        }
    }

    if (-not (Test-Path -LiteralPath $lockPath)) {
        throw "The pinned toolchain lock is missing: $lockPath"
    }
    $boundArtifactInputs = @(
        [pscustomobject]@{ path = $MyInvocation.MyCommand.Path; sha256 = $driverHash },
        [pscustomobject]@{ path = $lockPath; sha256 = $lockHash },
        [pscustomobject]@{ path = $schemaPath; sha256 = $schemaHash }
    )
    Assert-HashedFileIntegrity `
        -Inputs $boundArtifactInputs `
        -Description "Bound artifact input"
    $lockDocument = Get-Content -Raw -LiteralPath $lockPath | ConvertFrom-Json
    if ($lockDocument.schema -ne "vetra.verus-toolchain-lock" -or
        [int]$lockDocument.schema_version -ne 2 -or
        $null -eq $lockDocument.platforms) {
        throw "The pinned toolchain lock has an unsupported schema"
    }
    if (-not [string]::IsNullOrWhiteSpace($OfflineBundleRoot)) {
        if (-not [System.IO.Path]::IsPathRooted($OfflineBundleRoot)) {
            throw "-OfflineBundleRoot must be an absolute directory path"
        }
        $offlineBundleRootFull = [System.IO.Path]::GetFullPath($OfflineBundleRoot)
        if (-not (Test-Path -LiteralPath $offlineBundleRootFull -PathType Container)) {
            throw "The offline bundle directory is missing: $offlineBundleRootFull"
        }
    }
    $platformProperty = $lockDocument.platforms.PSObject.Properties[$platformKey]
    if ($null -eq $platformProperty) {
        throw "The pinned toolchain lock has no entry for $platformKey"
    }
    $lock = $platformProperty.Value
    $report.toolchain.declared = $lock
    if ([string]$lock.verus.platform -ne $expectedPlatformTriple -or
        [string]$lock.rustup.platform -ne $expectedPlatformTriple -or
        -not ([string]$lock.rust.toolchain).EndsWith(
            "-" + $expectedPlatformTriple,
            [System.StringComparison]::Ordinal)) {
        throw "The selected toolchain does not match $platformKey"
    }

    $verusArchiveName = Assert-SafeLeafName `
        -Name ([string]$lock.verus.archive) `
        -Description "Verus archive name"
    $rustupArchiveName = Assert-SafeLeafName `
        -Name ([string]$lock.rustup.archive) `
        -Description "rustup archive name"
    $verusVersionLeaf = Assert-SafeLeafName `
        -Name ([string]$lock.verus.version) `
        -Description "Verus version"
    $rustToolchainLeaf = Assert-SafeLeafName `
        -Name ([string]$lock.rust.toolchain) `
        -Description "Rust toolchain"
    if ([string]$lock.verus.sha256 -notmatch '^[0-9a-fA-F]{64}$' -or
        [string]$lock.rustup.sha256 -notmatch '^[0-9a-fA-F]{64}$') {
        throw "Toolchain archive hashes must be SHA256 values"
    }

    $tempRoot = [System.IO.Path]::GetFullPath(
        [System.IO.Path]::GetTempPath()).TrimEnd(
        [System.IO.Path]::DirectorySeparatorChar,
        [System.IO.Path]::AltDirectorySeparatorChar)
    $cacheRoot = Assert-PathWithinRoot `
        -Root $tempRoot `
        -Path (Join-Path $tempRoot "proveai-verus-m0")
    $runRoot = Assert-PathWithinRoot `
        -Root $tempRoot `
        -Path (Join-Path $tempRoot ("vetra-verus-run-" + $runId))
    if (Test-Path -LiteralPath $runRoot) {
        throw "Fresh verifier run directory already exists: $runRoot"
    }
    New-Item -ItemType Directory -Path $runRoot | Out-Null
    $sourceSnapshotRoot = Assert-PathWithinRoot `
        -Root $runRoot `
        -Path (Join-Path $runRoot "sources")
    New-Item -ItemType Directory -Path $sourceSnapshotRoot | Out-Null
    $report.source_snapshot.created_at_utc =
        [System.DateTimeOffset]::UtcNow.ToString("o")
    foreach ($target in $targets) {
        $sourceLeaf = Assert-SafeLeafName `
            -Name ([System.IO.Path]::GetFileName($target.SourcePath)) `
            -Description "Registered source name"
        $snapshotPath = Assert-PathWithinRoot `
            -Root $sourceSnapshotRoot `
            -Path (Join-Path $sourceSnapshotRoot $sourceLeaf)
        Copy-Item -LiteralPath $target.SourcePath -Destination $snapshotPath
        if ((Get-Sha256Lower -Path $snapshotPath) -ne
            $targetReportByName[$target.Name].source_sha256) {
            throw "Source changed while snapshotting $($target.Name)"
        }
        [System.IO.File]::SetAttributes(
            $snapshotPath,
            [System.IO.FileAttributes]::ReadOnly)
        $snapshotSourceByName[$target.Name] = $snapshotPath
    }
    Assert-RegisteredSourceHashes `
        -RegisteredTargets $targets `
        -ReportsByName $targetReportByName

    # Policy scans run on the hash-validated read-only snapshot rather than the
    # live tree, so the scanned bytes are exactly the bytes Verus verifies and
    # a concurrent writer cannot present different content to the scan and to
    # the verifier.
    $declaredSourceLookup = @{}
    foreach ($target in $targets) {
        $declaredSourceLookup[
            (Get-PathKey -Path $snapshotSourceByName[$target.Name])] = $target.Name
    }
    $validatedParentImports = 0
    for ($targetIndex = 0; $targetIndex -lt $targets.Count; $targetIndex++) {
        $target = $targets[$targetIndex]
        $targetReport = $targetReports[$targetIndex]
        $imports = @(Get-DirectPathImports `
            -SourcePath $snapshotSourceByName[$target.Name])
        $targetReport.direct_path_imports = @(
            $imports | ForEach-Object { $_.DeclaredPath })
        foreach ($import in $imports) {
            $importKey = Get-PathKey -Path $import.FullPath
            if (-not $declaredSourceLookup.ContainsKey($importKey)) {
                throw ("$($target.Name) directly imports an unregistered source: " +
                    $import.DeclaredPath)
            }
        }

        if ($target.ContributionParent -ne "__full__" -and
            $target.ContributionParent -ne "__skip__") {
            $parentName = $target.ContributionParent
            $parentIndex = -1
            for ($candidateIndex = 0; $candidateIndex -lt $targetIndex; $candidateIndex++) {
                if ($targets[$candidateIndex].Name -eq $parentName) {
                    $parentIndex = $candidateIndex
                    break
                }
            }
            if ($parentIndex -lt 0) {
                throw "$($target.Name) contribution parent is not an earlier target: $parentName"
            }
            if ($imports.Count -ne 1) {
                throw ("$($target.Name) must directly import exactly its declared " +
                    "contribution parent $parentName; found $($imports.Count) path imports")
            }
            $expectedParentPath = [System.IO.Path]::GetFullPath(
                $snapshotSourceByName[$parentName])
            if (-not $imports[0].FullPath.Equals(
                    $expectedParentPath,
                    [System.StringComparison]::OrdinalIgnoreCase)) {
                throw ("$($target.Name) contribution parent $parentName does not match " +
                    "its sole direct path import $($imports[0].DeclaredPath)")
            }
            $targetReport.immediate_parent_import_validated = $true
            $validatedParentImports++
        }
    }
    $report.policy.all_direct_path_imports_registered = $true
    $report.policy.cumulative_parent_imports_validated = $validatedParentImports
    $report.policy.simple_path_module_grammar_enforced = $true

    foreach ($target in $targets) {
        if (@($target.ExtraArguments).Count -ne 0) {
            throw "$($target.Name) contains nonempty ExtraArguments"
        }
        $forbidden = @(Select-String `
            -LiteralPath $snapshotSourceByName[$target.Name] `
            -CaseSensitive:$false `
            -Pattern $forbiddenProofPattern)
        if ($forbidden.Count -ne 0) {
            throw ("$($target.Name) contains a forbidden proof construct: " +
                $forbidden[0].Line.Trim())
        }
    }
    $report.policy.nonempty_extra_arguments_rejected = $true
    $report.policy.status = "passed"

    $snapshotMetadata = Assert-SourceSnapshot `
        -SnapshotRoot $sourceSnapshotRoot `
        -RegisteredTargets $targets `
        -ReportsByName $targetReportByName `
        -SnapshotPathsByName $snapshotSourceByName
    $report.source_snapshot.source_file_count = $snapshotMetadata.FileCount
    $report.source_snapshot.manifest_sha256 = $snapshotMetadata.Sha256
    $report.source_snapshot.exact_membership_validated = $true
    $report.source_snapshot.source_hashes_match_registry = $true
    $report.source_snapshot.all_files_read_only = $true

    $downloadDir = Assert-PathWithinRoot `
        -Root $cacheRoot `
        -Path (Join-Path $cacheRoot "downloads")
    $verusRoot = Assert-PathWithinRoot `
        -Root $cacheRoot `
        -Path (Join-Path $cacheRoot ("verus-" + $verusVersionLeaf))
    $cargoHome = Assert-PathWithinRoot `
        -Root $runRoot `
        -Path (Join-Path $runRoot "cargo")
    $rustupHome = Assert-PathWithinRoot `
        -Root $runRoot `
        -Path (Join-Path $runRoot "rustup")
    $rustupInit = Assert-PathWithinRoot `
        -Root $downloadDir `
        -Path (Join-Path $downloadDir $rustupArchiveName)
    $verusArchive = Assert-PathWithinRoot `
        -Root $downloadDir `
        -Path (Join-Path $downloadDir $verusArchiveName)
    $verusTreeRoot = Assert-PathWithinRoot `
        -Root $verusRoot `
        -Path (Join-Path $verusRoot $verusDirectoryLeaf)
    $verusExe = Assert-PathWithinRoot `
        -Root $verusTreeRoot `
        -Path (Join-Path $verusTreeRoot $verusExecutableLeaf)
    $verusZ3Exe = Assert-PathWithinRoot `
        -Root $verusTreeRoot `
        -Path (Join-Path $verusTreeRoot $verusZ3Leaf)

$cacheMutexName =
    if ($platformKey -eq "windows-x64") {
        "Local\ProveAI_Verified_M0_Cache_v2"
    }
    else {
        "ProveAI_Verified_M0_Cache_v2"
    }
$cacheMutex = New-Object System.Threading.Mutex(
    $false,
    $cacheMutexName)
$mutexHeld = $false
try {
    try {
        $mutexHeld = $cacheMutex.WaitOne([System.TimeSpan]::FromMinutes(30))
    }
    catch [System.Threading.AbandonedMutexException] {
        $mutexHeld = $true
    }
    if (-not $mutexHeld) {
        throw "Timed out waiting for the isolated verifier cache lock"
    }

    New-Item -ItemType Directory -Force -Path $downloadDir | Out-Null

function Get-VerifiedArtifact {
    param(
        [Parameter(Mandatory = $true)][string]$Uri,
        [Parameter(Mandatory = $true)][string]$Destination,
        [Parameter(Mandatory = $true)][string]$ExpectedSha256
    )

    $Destination = Assert-CacheChild $Destination
    $expected = $ExpectedSha256.ToUpperInvariant()
    if (Test-Path -LiteralPath $Destination) {
        $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $Destination).Hash
        if ($actual -eq $expected) {
            return
        }
        Remove-Item -Force -LiteralPath $Destination
    }

    $partial = Assert-CacheChild ($Destination + ".partial")
    Remove-Item -Force -LiteralPath $partial -ErrorAction SilentlyContinue
    try {
        Invoke-WebRequest -UseBasicParsing -Uri $Uri -OutFile $partial
        $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $partial).Hash
        if ($actual -ne $expected) {
            throw "SHA256 mismatch for $Uri; expected $expected, found $actual"
        }
        Move-Item -Force -LiteralPath $partial -Destination $Destination
    }
    finally {
        Remove-Item -Force -LiteralPath $partial -ErrorAction SilentlyContinue
    }
}

function Get-OfflineArtifact {
    param(
        [Parameter(Mandatory = $true)][string]$Source,
        [Parameter(Mandatory = $true)][string]$Destination,
        [Parameter(Mandatory = $true)][string]$ExpectedSha256
    )

    $sourcePath = Assert-PathWithinRoot `
        -Root $offlineBundleRootFull `
        -Path $Source
    if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
        throw "Offline bundle artifact is missing: $sourcePath"
    }
    $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).Hash
    if ($actual -ne $ExpectedSha256.ToUpperInvariant()) {
        throw "Offline bundle SHA256 mismatch for $sourcePath; expected $ExpectedSha256, found $actual"
    }
    Copy-Item -LiteralPath $sourcePath -Destination $Destination
}

function Assert-CacheChild {
    param([Parameter(Mandatory = $true)][string]$Path)

    Assert-PathWithinRoot -Root $cacheRoot -Path $Path
}

function Invoke-NativeCaptured {
    param(
        [Parameter(Mandatory = $true)][string]$FilePath,
        [Parameter(Mandatory = $true)][string[]]$Arguments
    )

    $savedPreference = $ErrorActionPreference
    try {
        $ErrorActionPreference = "Continue"
        $output = @(& $FilePath @Arguments 2>&1)
        $exitCode = $LASTEXITCODE
    }
    finally {
        $ErrorActionPreference = $savedPreference
    }
    [pscustomobject]@{
        ExitCode = $exitCode
        Output = $output
        Text = ($output | Out-String).Trim()
    }
}

    if ($null -ne $offlineBundleRootFull) {
        Get-OfflineArtifact `
            -Source (Join-Path (Join-Path $offlineBundleRootFull "archives") `
                $verusArchiveName) `
            -Destination $verusArchive `
            -ExpectedSha256 $lock.verus.sha256
        Get-OfflineArtifact `
            -Source (Join-Path (Join-Path $offlineBundleRootFull "archives") `
                $rustupArchiveName) `
            -Destination $rustupInit `
            -ExpectedSha256 $lock.rustup.sha256
    }
    else {
        Get-VerifiedArtifact `
            -Uri $lock.verus.url `
            -Destination $verusArchive `
            -ExpectedSha256 $lock.verus.sha256
        Get-VerifiedArtifact `
            -Uri $lock.rustup.url `
            -Destination $rustupInit `
            -ExpectedSha256 $lock.rustup.sha256
    }
    if ($platformKey -eq "linux-x64") {
        $chmodCommands = @(Get-Command "chmod" -CommandType Application `
            -ErrorAction SilentlyContinue)
        $chmodCommand =
            if ($chmodCommands.Count -eq 0) { $null } else { $chmodCommands[0] }
        if ($null -eq $chmodCommand) {
            throw "Linux verification requires chmod"
        }
        $chmodResult = Invoke-NativeCaptured `
            -FilePath $chmodCommand.Source `
            -Arguments @("0700", $rustupInit)
        if ($chmodResult.ExitCode -ne 0) {
            throw "Could not make the pinned rustup installer executable"
        }
    }
    $report.toolchain.observed.verus_archive_sha256 =
        Get-Sha256Lower -Path $verusArchive
    $report.toolchain.observed.rustup_archive_sha256 =
        Get-Sha256Lower -Path $rustupInit

    # Recreate the executable tree from the hash-checked archive on every run.
    # This prevents a modified cache entry from surviving behind a valid
    # version.txt file.
    $extracting = Assert-CacheChild ($verusRoot + ".extracting")
    $verifiedVerusRoot = Assert-CacheChild $verusRoot
    if (Test-Path -LiteralPath $extracting) {
        Remove-Item -Recurse -Force -LiteralPath $extracting
    }
    New-Item -ItemType Directory -Force -Path $extracting | Out-Null
    try {
        if ($platformKey -eq "linux-x64") {
            $unzipCommands = @(Get-Command "unzip" -CommandType Application `
                -ErrorAction SilentlyContinue)
            $unzipCommand =
                if ($unzipCommands.Count -eq 0) { $null } else { $unzipCommands[0] }
            if ($null -eq $unzipCommand) {
                throw "Linux verification requires unzip"
            }
            $unzipResult = Invoke-NativeCaptured `
                -FilePath $unzipCommand.Source `
                -Arguments @("-q", $verusArchive, "-d", $extracting)
            if ($unzipResult.ExitCode -ne 0) {
                throw ("The verified Verus archive could not be extracted: " +
                    $unzipResult.Text)
            }
        }
        else {
            Expand-Archive `
                -LiteralPath $verusArchive `
                -DestinationPath $extracting
        }
        if (-not (Test-Path -LiteralPath (
                    Join-Path (Join-Path $extracting $verusDirectoryLeaf) `
                        $verusExecutableLeaf)) -or
            -not (Test-Path -LiteralPath (
                    Join-Path (Join-Path $extracting $verusDirectoryLeaf) `
                        $verusZ3Leaf))) {
            throw "The verified Verus archive has an unexpected layout"
        }
        if (Test-Path -LiteralPath $verifiedVerusRoot) {
            Remove-Item -Recurse -Force -LiteralPath $verifiedVerusRoot
        }
        Move-Item -LiteralPath $extracting -Destination $verifiedVerusRoot
    }
    finally {
        if (Test-Path -LiteralPath $extracting) {
            Remove-Item -Recurse -Force -LiteralPath $extracting
        }
    }
    $report.toolchain.observed.verus_executable_sha256 =
        Get-Sha256Lower -Path $verusExe
    $verusTreeMetadata = Get-DeterministicTreeMetadata -Root $verusTreeRoot
    $report.toolchain.observed.verus_tree_sha256 =
        $verusTreeMetadata.Sha256
    $report.toolchain.observed.verus_tree_file_count =
        $verusTreeMetadata.FileCount

    $isolatedEnvironmentNames = @(
        "CARGO_HOME",
        "RUSTUP_HOME",
        "RUSTUP_TOOLCHAIN",
        "RUSTUP_DIST_SERVER",
        "RUSTUP_UPDATE_ROOT",
        "RUSTUP_NO_UPDATE_CHECK",
        "RUSTC",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC",
        "CARGO_TARGET_DIR",
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "RUSTC_BOOTSTRAP",
        "RUSTDOCFLAGS",
        "VERUS_Z3_PATH",
        "VERUS_SINGULAR_PATH",
        "VERUS_RUSTC",
        "VERUS_RUSTC_PATH",
        "Z3_EXE",
        "PATH"
    )
    $savedEnvironment = @{}
    foreach ($environmentName in $isolatedEnvironmentNames) {
        $savedEnvironment[$environmentName] =
            [System.Environment]::GetEnvironmentVariable(
                $environmentName,
                [System.EnvironmentVariableTarget]::Process)
    }

    $rustupDistServer = if ($null -ne $offlineBundleRootFull) {
        "offline-bundle"
    }
    else {
        "https://static.rust-lang.org"
    }
    $rustupUpdateRoot = if ($null -ne $offlineBundleRootFull) {
        "offline-bundle"
    }
    else {
        "https://static.rust-lang.org/rustup"
    }

    try {
        [System.Environment]::SetEnvironmentVariable(
            "CARGO_HOME", $cargoHome,
            [System.EnvironmentVariableTarget]::Process)
        [System.Environment]::SetEnvironmentVariable(
            "RUSTUP_HOME", $rustupHome,
            [System.EnvironmentVariableTarget]::Process)
        [System.Environment]::SetEnvironmentVariable(
            "RUSTUP_TOOLCHAIN", $rustToolchainLeaf,
            [System.EnvironmentVariableTarget]::Process)
        [System.Environment]::SetEnvironmentVariable(
            "RUSTUP_DIST_SERVER", $rustupDistServer,
            [System.EnvironmentVariableTarget]::Process)
        [System.Environment]::SetEnvironmentVariable(
            "RUSTUP_UPDATE_ROOT", $rustupUpdateRoot,
            [System.EnvironmentVariableTarget]::Process)
        [System.Environment]::SetEnvironmentVariable(
            "RUSTUP_NO_UPDATE_CHECK", "1",
            [System.EnvironmentVariableTarget]::Process)
        foreach ($clearedName in @(
                "RUSTC",
                "RUSTC_WRAPPER",
                "RUSTC_WORKSPACE_WRAPPER",
                "CARGO_BUILD_RUSTC",
                "CARGO_TARGET_DIR",
                "RUSTFLAGS",
                "CARGO_ENCODED_RUSTFLAGS",
                "RUSTC_BOOTSTRAP",
                "RUSTDOCFLAGS",
                "VERUS_Z3_PATH",
                "VERUS_SINGULAR_PATH",
                "VERUS_RUSTC",
                "VERUS_RUSTC_PATH",
                "Z3_EXE")) {
            [System.Environment]::SetEnvironmentVariable(
                $clearedName,
                $null,
                [System.EnvironmentVariableTarget]::Process)
        }
        [System.Environment]::SetEnvironmentVariable(
            "VERUS_Z3_PATH", $verusZ3Exe,
            [System.EnvironmentVariableTarget]::Process)
        [System.Environment]::SetEnvironmentVariable(
            "PATH",
            (Join-Path $cargoHome "bin") +
                [System.IO.Path]::PathSeparator +
                $savedEnvironment["PATH"],
            [System.EnvironmentVariableTarget]::Process)
        $report.toolchain.observed.rustup_dist_server =
            $rustupDistServer
        $report.toolchain.observed.rustup_update_root =
            $rustupUpdateRoot

        $rustupExe = Assert-PathWithinRoot `
            -Root $cargoHome `
            -Path (Join-Path (Join-Path $cargoHome "bin") `
                $rustupExecutableLeaf)
        if ((Test-Path -LiteralPath $cargoHome) -or
            (Test-Path -LiteralPath $rustupHome)) {
            throw "Fresh Rust homes unexpectedly existed before installation"
        }
        if ($null -ne $offlineBundleRootFull) {
            $offlineRustup = Assert-PathWithinRoot `
                -Root $offlineBundleRootFull `
                -Path (Join-Path (Join-Path $offlineBundleRootFull "rustup") `
                    $rustupExecutableLeaf)
            $offlineToolchain = Assert-PathWithinRoot `
                -Root $offlineBundleRootFull `
                -Path (Join-Path (Join-Path $offlineBundleRootFull "toolchains") `
                    $rustToolchainLeaf)
            if (-not (Test-Path -LiteralPath $offlineRustup -PathType Leaf) -or
                -not (Test-Path -LiteralPath $offlineToolchain -PathType Container)) {
                throw "Offline bundle is missing the pinned Rust executable or toolchain"
            }
            New-Item -ItemType Directory -Force -Path (Join-Path $cargoHome "bin") | Out-Null
            Copy-Item -LiteralPath $offlineRustup -Destination $rustupExe
            New-Item -ItemType Directory -Force -Path (Join-Path $rustupHome "toolchains") | Out-Null
            Copy-Item -LiteralPath $offlineToolchain `
                -Destination (Join-Path $rustupHome "toolchains") -Recurse
            if ($platformKey -eq "linux-x64") {
                $chmodCommands = @(Get-Command "chmod" -CommandType Application `
                    -ErrorAction SilentlyContinue)
                if ($chmodCommands.Count -eq 0) {
                    throw "Linux verification requires chmod"
                }
                $chmodResult = Invoke-NativeCaptured `
                    -FilePath $chmodCommands[0].Source `
                    -Arguments @("0700", $rustupExe)
                if ($chmodResult.ExitCode -ne 0) {
                    throw "Could not make the staged rustup executable runnable"
                }
            }
        }
        else {
            $rustupInstallResult = Invoke-NativeCaptured `
                -FilePath $rustupInit `
                -Arguments @(
                    "-y",
                    "--no-modify-path",
                    "--profile", "minimal",
                    "--default-toolchain", "none")
            if ($rustupInstallResult.ExitCode -ne 0) {
                throw ("The fresh rustup installation failed: " +
                    $rustupInstallResult.Text)
            }
        }
        if (-not (Test-Path -LiteralPath $rustupExe -PathType Leaf)) {
            throw "The Rust setup did not create $rustupExecutableLeaf"
        }

        $installedRustupHash = (
            Get-FileHash -Algorithm SHA256 -LiteralPath $rustupExe).Hash
        if ($installedRustupHash -ne $lock.rustup.sha256.ToUpperInvariant()) {
            throw "The installed rustup executable does not match the pinned archive"
        }
        $report.toolchain.observed.rustup_executable_sha256 =
            $installedRustupHash.ToLowerInvariant()

        $autoUpdateResult = Invoke-NativeCaptured -FilePath $rustupExe `
            -Arguments @("set", "auto-self-update", "disable")
        if ($autoUpdateResult.ExitCode -ne 0) {
            throw "Could not disable rustup self-update in the isolated cache"
        }

        # Query rustup itself without resolving the not-yet-installed selected
        # toolchain.  Otherwise `rustup --version` may implicitly download that
        # toolchain before the explicit, checked installation below.
        [System.Environment]::SetEnvironmentVariable(
            "RUSTUP_TOOLCHAIN",
            $null,
            [System.EnvironmentVariableTarget]::Process)
        try {
            $rustupResult = Invoke-NativeCaptured -FilePath $rustupExe `
                -Arguments @("--version")
        }
        finally {
            [System.Environment]::SetEnvironmentVariable(
                "RUSTUP_TOOLCHAIN",
                $rustToolchainLeaf,
                [System.EnvironmentVariableTarget]::Process)
        }
        if ($rustupResult.ExitCode -ne 0) {
            throw "Unexpected rustup version: $($rustupResult.Text)"
        }
        $rustupVersionPattern = "^rustup " +
            [regex]::Escape($lock.rustup.version) + "(?:\s|$)"
        $rustupVersionLine = Get-CanonicalVersionLine `
            -Text $rustupResult.Text `
            -Pattern $rustupVersionPattern `
            -ToolName "rustup"
        $report.toolchain.observed.rustup_version = $rustupVersionLine

        if ($null -eq $offlineBundleRootFull) {
            $toolchainInstallResult = Invoke-NativeCaptured `
                -FilePath $rustupExe `
                -Arguments @(
                    "toolchain", "install", $rustToolchainLeaf,
                    "--profile", "minimal")
            if ($toolchainInstallResult.ExitCode -ne 0) {
                throw ("The exact Rust toolchain installation failed: " +
                    $toolchainInstallResult.Text)
            }
        }

        $toolchainRoot = Assert-PathWithinRoot `
            -Root $rustupHome `
            -Path (Join-Path (Join-Path $rustupHome "toolchains") `
                $rustToolchainLeaf)
        $rustcExe = Assert-PathWithinRoot `
            -Root $toolchainRoot `
            -Path (Join-Path (Join-Path $toolchainRoot "bin") `
                $rustcExecutableLeaf)
        $cargoExe = Assert-PathWithinRoot `
            -Root $toolchainRoot `
            -Path (Join-Path (Join-Path $toolchainRoot "bin") `
                $cargoExecutableLeaf)
        $targetLib = Assert-PathWithinRoot `
            -Root $toolchainRoot `
            -Path (Join-Path (
                Join-Path (
                    Join-Path $toolchainRoot "lib") `
                    "rustlib") `
                (Join-Path $expectedPlatformTriple "lib"))
        if (-not (Test-Path -LiteralPath $rustcExe -PathType Leaf) -or
            -not (Test-Path -LiteralPath $cargoExe -PathType Leaf) -or
            -not (Test-Path -LiteralPath $targetLib -PathType Container)) {
            throw "The exact Rust toolchain has an unexpected layout"
        }

        $installedRustupHash = (
            Get-FileHash -Algorithm SHA256 -LiteralPath $rustupExe).Hash
        if ($installedRustupHash -ne $lock.rustup.sha256.ToUpperInvariant()) {
            throw "rustup changed during pinned toolchain installation"
        }

        $rustcResult = Invoke-NativeCaptured -FilePath $rustcExe `
            -Arguments @("--version")
        $expectedRustVersion = ($lock.rust.toolchain -split '-', 2)[0]
        if ($rustcResult.ExitCode -ne 0) {
            throw "Unexpected Rust toolchain version: $($rustcResult.Text)"
        }
        $rustcVersionPattern = "^rustc " +
            [regex]::Escape($expectedRustVersion) + "(?:\s|$)"
        $rustcVersionLine = Get-CanonicalVersionLine `
            -Text $rustcResult.Text `
            -Pattern $rustcVersionPattern `
            -ToolName "rustc"
        $report.toolchain.observed.rustc_executable_sha256 =
            Get-Sha256Lower -Path $rustcExe
        $report.toolchain.observed.rustc_version = $rustcVersionLine
        $report.toolchain.observed.cargo_executable_sha256 =
            Get-Sha256Lower -Path $cargoExe
        $toolchainMetadata = Get-DeterministicTreeMetadata -Root $toolchainRoot
        $report.toolchain.observed.rust_toolchain_tree_sha256 =
            $toolchainMetadata.Sha256
        $report.toolchain.observed.rust_toolchain_file_count =
            $toolchainMetadata.FileCount
        $report.toolchain.observed.fresh_rust_environment = $true

        $verusVersion = Get-Content -Raw -LiteralPath (
            Join-Path $verusTreeRoot "version.txt")
        if ($verusVersion.Trim() -ne $lock.verus.version) {
            throw "Unexpected Verus version: $($verusVersion.Trim())"
        }
        $report.toolchain.observed.verus_version = $verusVersion.Trim()

        $nonDuplicatedVerified = 0
        $verifiedCounts = @{}
        foreach ($target in $targets) {
            $targetReport = $targetReportByName[$target.Name]
            $targetStarted = [System.DateTimeOffset]::UtcNow
            $targetReport.status = "running"
            $targetReport.started_at_utc = $targetStarted.ToString("o")
            try {
                Assert-HashedFileIntegrity `
                    -Inputs $boundArtifactInputs `
                    -Description "Bound artifact input"
                $null = Assert-SourceSnapshot `
                    -SnapshotRoot $sourceSnapshotRoot `
                    -RegisteredTargets $targets `
                    -ReportsByName $targetReportByName `
                    -SnapshotPathsByName $snapshotSourceByName `
                    -ExpectedTreeSha256 $report.source_snapshot.manifest_sha256
                $report.source_snapshot.pre_target_validation_count++
                Write-Host ("Verifying " + $target.Name + "...")
                $arguments = @(
                    $snapshotSourceByName[$target.Name],
                    "--crate-type",
                    "lib",
                    "--no-cheating"
                )
                $verusResult = Invoke-NativeCaptured -FilePath $verusExe `
                    -Arguments $arguments
                $targetReport.verus_exit_code = $verusResult.ExitCode
                $verusResult.Output | ForEach-Object { Write-Host $_ }
                if ($verusResult.ExitCode -ne 0) {
                    throw "Verus rejected $($target.Name)"
                }
                $result = [regex]::Match(
                    $verusResult.Text,
                    "(\d+) verified, (\d+) errors")
                if (-not $result.Success) {
                    throw ("Could not parse a Verus obligation count for " +
                        $target.Name)
                }
                $verusErrors = [int]$result.Groups[2].Value
                $targetReport.verus_errors = $verusErrors
                if ($verusErrors -ne 0) {
                    throw ("Could not confirm a zero-error Verus obligation count for " +
                        $target.Name)
                }
                $null = Assert-SourceSnapshot `
                    -SnapshotRoot $sourceSnapshotRoot `
                    -RegisteredTargets $targets `
                    -ReportsByName $targetReportByName `
                    -SnapshotPathsByName $snapshotSourceByName `
                    -ExpectedTreeSha256 $report.source_snapshot.manifest_sha256
                $report.source_snapshot.post_target_validation_count++
                Assert-HashedFileIntegrity `
                    -Inputs $boundArtifactInputs `
                    -Description "Bound artifact input"
                $verified = [int]$result.Groups[1].Value
                if ($verified -le 0) {
                    throw ("Could not confirm a nonzero Verus obligation count for " +
                        $target.Name)
                }
                $verifiedCounts[$target.Name] = $verified
                $delta = 0
                if ($target.ContributionParent -eq "__full__") {
                    $delta = $verified
                }
                elseif ($target.ContributionParent -ne "__skip__") {
                    $parent = $target.ContributionParent
                    if (-not $verifiedCounts.ContainsKey($parent)) {
                        throw "$($target.Name) contribution parent was not verified first: $parent"
                    }
                    $delta = $verified - [int]$verifiedCounts[$parent]
                    if ($delta -lt 0) {
                        throw "$($target.Name) verified fewer obligations than parent $parent"
                    }
                }
                $nonDuplicatedVerified += $delta
                $sumOfTargetObligations += $verified
                $verifiedTargetCount++
                $targetReport.verified_obligations_total = $verified
                $targetReport.contribution_delta = $delta
                $targetReport.non_duplicated_total_after = $nonDuplicatedVerified
                $targetReport.status = "passed"
                $report.summary.verified_target_count = $verifiedTargetCount
                $report.summary.sum_of_target_obligations = $sumOfTargetObligations
                $report.summary.non_duplicated_verified_obligations =
                    $nonDuplicatedVerified
                Write-Host ("$($target.Name) verified obligations: " + $verified)
            }
            catch {
                $targetReport.status = "failed"
                $targetReport.error = $_.Exception.Message
                throw
            }
            finally {
                $targetCompleted = [System.DateTimeOffset]::UtcNow
                $targetReport.completed_at_utc = $targetCompleted.ToString("o")
                $targetReport.duration_ms = [long](
                    ($targetCompleted - $targetStarted).TotalMilliseconds)
            }
        }
        $null = Assert-SourceSnapshot `
            -SnapshotRoot $sourceSnapshotRoot `
            -RegisteredTargets $targets `
            -ReportsByName $targetReportByName `
            -SnapshotPathsByName $snapshotSourceByName `
            -ExpectedTreeSha256 $report.source_snapshot.manifest_sha256
        $null = Assert-TreeHash `
            -Root $toolchainRoot `
            -ExpectedSha256 $toolchainMetadata.Sha256 `
            -Description "The exact Rust toolchain tree"
        Assert-HashedFileIntegrity `
            -Inputs @(
                [pscustomobject]@{
                    path = $verusArchive
                    sha256 = $report.toolchain.observed.verus_archive_sha256
                },
                [pscustomobject]@{
                    path = $verusExe
                    sha256 = $report.toolchain.observed.verus_executable_sha256
                },
                [pscustomobject]@{
                    path = $rustupInit
                    sha256 = $report.toolchain.observed.rustup_archive_sha256
                }
            ) `
            -Description "Pinned verifier artifact"
        $null = Assert-TreeHash `
            -Root $verusTreeRoot `
            -ExpectedSha256 $verusTreeMetadata.Sha256 `
            -Description "The extracted Verus tool tree"
        $report.source_snapshot.final_validation_passed = $true
        $report.toolchain.observed.rust_toolchain_tree_unchanged = $true
        $report.toolchain.observed.verus_tree_unchanged = $true
        Write-Host ("Non-duplicated verified artifact obligations: " +
            $nonDuplicatedVerified)
    }
    finally {
        foreach ($environmentName in $isolatedEnvironmentNames) {
            [System.Environment]::SetEnvironmentVariable(
                $environmentName,
                $savedEnvironment[$environmentName],
                [System.EnvironmentVariableTarget]::Process)
        }
    }
}
finally {
    if ($mutexHeld) {
        $cacheMutex.ReleaseMutex()
    }
    $cacheMutex.Dispose()
}
    Assert-RegisteredSourceHashes `
        -RegisteredTargets $targets `
        -ReportsByName $targetReportByName
    Assert-HashedFileIntegrity `
        -Inputs $boundArtifactInputs `
        -Description "Bound artifact input"
    Remove-FreshRunRoot -RunRoot $runRoot
    if (Test-Path -LiteralPath $runRoot) {
        throw "The fresh verifier run directory could not be removed"
    }
    $report.source_snapshot.removed_after_run = $true
    $report.status = "passed"
    Assert-PassedReportSemanticConsistency -Report $report
}
catch {
    $report.status = "failed"
    $report.error = [pscustomobject][ordered]@{
        type = $_.Exception.GetType().FullName
        message = $_.Exception.Message
    }
    throw
}
finally {
    if ($null -ne $runRoot -and (Test-Path -LiteralPath $runRoot)) {
        try {
            Remove-FreshRunRoot -RunRoot $runRoot
            $report.source_snapshot.removed_after_run =
                -not (Test-Path -LiteralPath $runRoot)
        }
        catch {
            [Console]::Error.WriteLine(
                "Could not remove fresh verifier run directory: " +
                $_.Exception.Message)
        }
    }
    $runCompleted = [System.DateTimeOffset]::UtcNow
    $report.completed_at_utc = $runCompleted.ToString("o")
    $report.duration_ms = [long](($runCompleted - $runStarted).TotalMilliseconds)
    if (-not $NoReport) {
        try {
            Write-VerificationReport -Report $report -Destination $ReportPath
            Write-Host ("Verification report: " + $ReportPath)
        }
        catch {
            if ($report.status -eq "failed") {
                [Console]::Error.WriteLine(
                    "Could not write failed verification report: " +
                    $_.Exception.Message)
            }
            else {
                throw
            }
        }
    }
}
