[CmdletBinding()]
param()

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

if ([System.Environment]::OSVersion.Platform -ne
        [System.PlatformID]::Win32NT -or
    -not [System.Environment]::Is64BitOperatingSystem -or
    -not [System.Environment]::Is64BitProcess -or
    [System.Runtime.InteropServices.RuntimeInformation]::OSArchitecture -ne
        [System.Runtime.InteropServices.Architecture]::X64) {
    throw "The verified core is pinned to 64-bit Windows on x86-64"
}

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$lockPath = Join-Path $scriptDir "toolchain.lock.json"
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
        Name = "T5-C0"
        SourcePath = Join-Path $scriptDir "t5_commit_contextual.rs"
        ExtraArguments = @()
        ContributionParent = "T5-R0"
    }
)

# Fail closed when a new mechanized crate is added without being registered.
$declaredSources = @($targets | ForEach-Object {
    [System.IO.Path]::GetFullPath($_.SourcePath).ToLowerInvariant()
} | Sort-Object -Unique)
$presentSources = @(Get-ChildItem -LiteralPath $scriptDir -Filter "*.rs" -File |
    ForEach-Object { $_.FullName.ToLowerInvariant() } | Sort-Object -Unique)
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

$lock = Get-Content -Raw -LiteralPath $lockPath | ConvertFrom-Json

$tempRoot = [System.IO.Path]::GetFullPath($env:TEMP).TrimEnd(
    [System.IO.Path]::DirectorySeparatorChar,
    [System.IO.Path]::AltDirectorySeparatorChar)
$cacheRoot = [System.IO.Path]::GetFullPath(
    (Join-Path $tempRoot "proveai-verus-m0"))
$requiredPrefix = $tempRoot + [System.IO.Path]::DirectorySeparatorChar
if (-not $cacheRoot.StartsWith(
        $requiredPrefix,
        [System.StringComparison]::OrdinalIgnoreCase)) {
    throw "Verifier cache must remain below TEMP: $cacheRoot"
}

$downloadDir = Join-Path $cacheRoot "downloads"
$verusRoot = Join-Path $cacheRoot ("verus-" + $lock.verus.version)
$cargoHome = Join-Path $cacheRoot "cargo"
$rustupHome = Join-Path $cacheRoot "rustup"
$rustupInit = Join-Path $downloadDir $lock.rustup.archive
$verusArchive = Join-Path $downloadDir $lock.verus.archive
$verusExe = Join-Path $verusRoot "verus-x86-win\verus.exe"

$cacheMutex = New-Object System.Threading.Mutex(
    $false,
    "Local\ProveAI_Verified_M0_Cache_v1")
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

    $expected = $ExpectedSha256.ToUpperInvariant()
    if (Test-Path -LiteralPath $Destination) {
        $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $Destination).Hash
        if ($actual -eq $expected) {
            return
        }
        Remove-Item -Force -LiteralPath $Destination
    }

    $partial = $Destination + ".partial"
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

function Assert-CacheChild {
    param([Parameter(Mandatory = $true)][string]$Path)

    $fullPath = [System.IO.Path]::GetFullPath($Path)
    $cachePrefix = $cacheRoot.TrimEnd(
        [System.IO.Path]::DirectorySeparatorChar,
        [System.IO.Path]::AltDirectorySeparatorChar) +
        [System.IO.Path]::DirectorySeparatorChar
    if (-not $fullPath.StartsWith(
            $cachePrefix,
            [System.StringComparison]::OrdinalIgnoreCase)) {
        throw "Refusing a cache operation outside $cacheRoot`: $fullPath"
    }
    $fullPath
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

    Get-VerifiedArtifact `
        -Uri $lock.verus.url `
        -Destination $verusArchive `
        -ExpectedSha256 $lock.verus.sha256
    Get-VerifiedArtifact `
        -Uri $lock.rustup.url `
        -Destination $rustupInit `
        -ExpectedSha256 $lock.rustup.sha256

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
        Expand-Archive -LiteralPath $verusArchive -DestinationPath $extracting
        if (-not (Test-Path -LiteralPath (
                    Join-Path $extracting "verus-x86-win\verus.exe"))) {
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

    foreach ($target in $targets) {
        if (-not (Test-Path -LiteralPath $target.SourcePath)) {
            throw "$($target.Name) source is missing: $($target.SourcePath)"
        }
        $forbidden = @(Select-String -LiteralPath $target.SourcePath `
            -CaseSensitive:$false `
            -Pattern '\b(assume|admit|external_body|external_fn_specification|assume_specification|axiom|get_Some)\b|verifier::external')
        if ($forbidden.Count -ne 0) {
            throw ("$($target.Name) contains a forbidden proof construct: " +
                $forbidden[0].Line.Trim())
        }
    }

    $savedEnvironment = @{
        CARGO_HOME = $env:CARGO_HOME
        RUSTUP_HOME = $env:RUSTUP_HOME
        RUSTUP_TOOLCHAIN = $env:RUSTUP_TOOLCHAIN
        PATH = $env:PATH
    }

    try {
        $env:CARGO_HOME = $cargoHome
        $env:RUSTUP_HOME = $rustupHome
        $env:RUSTUP_TOOLCHAIN = $lock.rust.toolchain
        $env:PATH = (Join-Path $cargoHome "bin") + ";" + $savedEnvironment.PATH

        $rustupExe = Join-Path $cargoHome "bin\rustup.exe"
        if (-not (Test-Path -LiteralPath $rustupExe)) {
            & $rustupInit -y --no-modify-path --profile minimal `
                --default-toolchain none
            if ($LASTEXITCODE -ne 0) {
                throw "The isolated rustup installation failed"
            }
        }

        $installedRustupHash = (
            Get-FileHash -Algorithm SHA256 -LiteralPath $rustupExe).Hash
        if ($installedRustupHash -ne $lock.rustup.sha256.ToUpperInvariant()) {
            throw "The installed rustup executable does not match the pinned archive"
        }

        $autoUpdateResult = Invoke-NativeCaptured -FilePath $rustupExe `
            -Arguments @("set", "auto-self-update", "disable")
        if ($autoUpdateResult.ExitCode -ne 0) {
            throw "Could not disable rustup self-update in the isolated cache"
        }

        $rustupResult = Invoke-NativeCaptured -FilePath $rustupExe `
            -Arguments @("--version")
        if ($rustupResult.ExitCode -ne 0 -or
            $rustupResult.Text -notmatch ("rustup " + [regex]::Escape($lock.rustup.version))) {
            throw "Unexpected rustup version: $($rustupResult.Text)"
        }

        $toolchainRoot = Join-Path $rustupHome ("toolchains\" + $lock.rust.toolchain)
        $rustcExe = Join-Path $toolchainRoot "bin\rustc.exe"
        $cargoExe = Join-Path $toolchainRoot "bin\cargo.exe"
        $targetLib = Join-Path $toolchainRoot (
            "lib\rustlib\x86_64-pc-windows-msvc\lib")
        if (-not (Test-Path -LiteralPath $rustcExe) -or
            -not (Test-Path -LiteralPath $cargoExe) -or
            -not (Test-Path -LiteralPath $targetLib)) {
            & $rustupExe toolchain install $lock.rust.toolchain --profile minimal
            if ($LASTEXITCODE -ne 0) {
                throw "The pinned Rust toolchain installation failed"
            }
        }

        $installedRustupHash = (
            Get-FileHash -Algorithm SHA256 -LiteralPath $rustupExe).Hash
        if ($installedRustupHash -ne $lock.rustup.sha256.ToUpperInvariant()) {
            throw "rustup changed during pinned toolchain installation"
        }

        $rustcResult = Invoke-NativeCaptured -FilePath $rustcExe `
            -Arguments @("--version")
        if ($rustcResult.ExitCode -ne 0 -or
            $rustcResult.Text -notmatch "rustc 1\.96\.0") {
            throw "Unexpected Rust toolchain version: $($rustcResult.Text)"
        }

        $verusVersion = Get-Content -Raw -LiteralPath (
            Join-Path $verusRoot "verus-x86-win\version.txt")
        if ($verusVersion.Trim() -ne $lock.verus.version) {
            throw "Unexpected Verus version: $($verusVersion.Trim())"
        }

        $nonDuplicatedVerified = 0
        $verifiedCounts = @{}
        foreach ($target in $targets) {
            Write-Host ("Verifying " + $target.Name + "...")
            $arguments = @(
                $target.SourcePath,
                "--crate-type",
                "lib",
                "--no-cheating"
            ) + @($target.ExtraArguments)
            $verusResult = Invoke-NativeCaptured -FilePath $verusExe `
                -Arguments $arguments
            $verusResult.Output | ForEach-Object { Write-Host $_ }
            if ($verusResult.ExitCode -ne 0) {
                throw "Verus rejected $($target.Name)"
            }
            $result = [regex]::Match(
                $verusResult.Text,
                "(\d+) verified, (\d+) errors")
            if (-not $result.Success -or [int]$result.Groups[2].Value -ne 0) {
                throw ("Could not confirm a zero-error Verus obligation count for " +
                    $target.Name)
            }
            $verified = [int]$result.Groups[1].Value
            $verifiedCounts[$target.Name] = $verified
            if ($target.ContributionParent -eq "__full__") {
                $nonDuplicatedVerified += $verified
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
                $nonDuplicatedVerified += $delta
            }
            Write-Host ("$($target.Name) verified obligations: " + $verified)
        }
        Write-Host ("Non-duplicated verified artifact obligations: " +
            $nonDuplicatedVerified)
    }
    finally {
        $env:CARGO_HOME = $savedEnvironment.CARGO_HOME
        $env:RUSTUP_HOME = $savedEnvironment.RUSTUP_HOME
        $env:RUSTUP_TOOLCHAIN = $savedEnvironment.RUSTUP_TOOLCHAIN
        $env:PATH = $savedEnvironment.PATH
    }
}
finally {
    if ($mutexHeld) {
        $cacheMutex.ReleaseMutex()
    }
    $cacheMutex.Dispose()
}
