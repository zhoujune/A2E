[CmdletBinding()]
param(
    [Parameter(Mandatory = $true, Position = 0)]
    [string]$Target
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$lockPath = Join-Path $scriptDir "toolchain.lock.json"
$targetPattern = '^[A-Za-z0-9][A-Za-z0-9._-]*\.rs$'
if ($Target -notmatch $targetPattern -or
    [IO.Path]::IsPathRooted($Target) -or
    [IO.Path]::GetFileName($Target) -cne $Target) {
    throw "Target must be a safe .rs leaf filename: $Target"
}

$sourcePath = [IO.Path]::GetFullPath((Join-Path $scriptDir $Target))
$sourceRoot = [IO.Path]::GetFullPath($scriptDir).TrimEnd('\') + '\'
if (-not $sourcePath.StartsWith(
        $sourceRoot,
        [StringComparison]::OrdinalIgnoreCase) -or
    -not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
    throw "Target is not a mechanized source file: $Target"
}
$sourceHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $sourcePath).
    Hash.ToLowerInvariant()

function Get-Sha256Lower {
    param([Parameter(Mandatory = $true)][string]$Path)

    (Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant()
}

function Get-PinnedFile {
    param(
        [Parameter(Mandatory = $true)][string]$Path,
        [Parameter(Mandatory = $true)][string]$Uri,
        [Parameter(Mandatory = $true)][string]$Sha256
    )

    if (Test-Path -LiteralPath $Path -PathType Leaf) {
        if ((Get-Sha256Lower -Path $Path) -ceq $Sha256) {
            return
        }
        throw "Cached artifact hash mismatch: $Path"
    }

    $partial = "$Path.partial-$PID"
    try {
        Invoke-WebRequest -UseBasicParsing -Uri $Uri -OutFile $partial
        if ((Get-Sha256Lower -Path $partial) -cne $Sha256) {
            throw "Downloaded artifact hash mismatch: $Uri"
        }
        Move-Item -LiteralPath $partial -Destination $Path
    }
    finally {
        Remove-Item -Force -LiteralPath $partial -ErrorAction SilentlyContinue
    }
}

function Invoke-Checked {
    param(
        [Parameter(Mandatory = $true)][string]$FilePath,
        [Parameter(Mandatory = $true)][string[]]$Arguments,
        [Parameter(Mandatory = $true)][string]$Description
    )

    & $FilePath @Arguments
    if ($LASTEXITCODE -ne 0) {
        throw "$Description failed with exit code $LASTEXITCODE"
    }
}

if (-not (Test-Path -LiteralPath $lockPath -PathType Leaf)) {
    throw "Pinned toolchain lock is missing: $lockPath"
}
$lock = Get-Content -Raw -LiteralPath $lockPath | ConvertFrom-Json
$verusVersion = [string]$lock.verus.version
$rustToolchain = [string]$lock.rust.toolchain
$verusArchiveName = [string]$lock.verus.archive
$rustupArchiveName = [string]$lock.rustup.archive
$safeLeafPattern = '^[A-Za-z0-9][A-Za-z0-9._+-]*$'
if ($verusVersion -notmatch $safeLeafPattern -or
    $rustToolchain -notmatch $safeLeafPattern -or
    $verusArchiveName -notmatch $safeLeafPattern -or
    $rustupArchiveName -notmatch $safeLeafPattern -or
    [string]$lock.verus.sha256 -notmatch '^[0-9a-fA-F]{64}$' -or
    [string]$lock.rustup.sha256 -notmatch '^[0-9a-fA-F]{64}$') {
    throw "toolchain.lock.json contains an unsafe or invalid pinned value"
}

$temporaryRoot = [IO.Path]::GetFullPath($env:TEMP).TrimEnd('\')
$cacheRoot = Join-Path $temporaryRoot "proveai-verus-m0"
$downloadRoot = Join-Path $cacheRoot "downloads"
$developmentRoot = Join-Path $temporaryRoot "proveai-verus-check-target-v1"
$runRoot = Join-Path $temporaryRoot (
    "proveai-check-target-" + [guid]::NewGuid().ToString("N"))
$cargoHome = Join-Path $developmentRoot "cargo"
$rustupHome = Join-Path $developmentRoot "rustup"
$verusArchive = Join-Path $downloadRoot $verusArchiveName
$rustupInit = Join-Path $downloadRoot $rustupArchiveName
$rustupExe = Join-Path $cargoHome "bin\rustup.exe"
$toolchainRoot = Join-Path $rustupHome ("toolchains\" + $rustToolchain)
$rustcExe = Join-Path $toolchainRoot "bin\rustc.exe"
$verusExe = Join-Path $runRoot "verus-x86-win\verus.exe"

$environmentNames = @(
    "CARGO_HOME", "RUSTUP_HOME", "RUSTUP_TOOLCHAIN",
    "RUSTUP_DIST_SERVER", "RUSTUP_UPDATE_ROOT", "RUSTUP_NO_UPDATE_CHECK",
    "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC", "CARGO_TARGET_DIR", "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS", "RUSTC_BOOTSTRAP", "RUSTDOCFLAGS",
    "VERUS_Z3_PATH", "VERUS_SINGULAR_PATH", "VERUS_RUSTC",
    "VERUS_RUSTC_PATH", "Z3_EXE", "PATH"
)
$savedEnvironment = @{}
foreach ($name in $environmentNames) {
    $savedEnvironment[$name] = [Environment]::GetEnvironmentVariable($name)
}

$mutex = [Threading.Mutex]::new($false, "Local\ProveAI_Verified_M0_Cache_v1")
$mutexHeld = $false
try {
    try {
        $mutexHeld = $mutex.WaitOne([TimeSpan]::FromMinutes(30))
    }
    catch [Threading.AbandonedMutexException] {
        $mutexHeld = $true
    }
    if (-not $mutexHeld) {
        throw "Timed out waiting for the pinned verifier cache"
    }

    New-Item -ItemType Directory -Force -Path $downloadRoot | Out-Null
    New-Item -ItemType Directory -Path $runRoot | Out-Null
    Get-PinnedFile -Path $verusArchive -Uri ([string]$lock.verus.url) `
        -Sha256 ([string]$lock.verus.sha256).ToLowerInvariant()
    Get-PinnedFile -Path $rustupInit -Uri ([string]$lock.rustup.url) `
        -Sha256 ([string]$lock.rustup.sha256).ToLowerInvariant()
    Expand-Archive -LiteralPath $verusArchive -DestinationPath $runRoot
    if (-not (Test-Path -LiteralPath $verusExe -PathType Leaf)) {
        throw "Pinned Verus archive has an unexpected layout"
    }
    $observedVerusVersion = (Get-Content -Raw -LiteralPath (
        Join-Path (Split-Path -Parent $verusExe) "version.txt")).Trim()
    if ($observedVerusVersion -cne $verusVersion) {
        throw "Unexpected Verus version: $observedVerusVersion"
    }

    $env:CARGO_HOME = $cargoHome
    $env:RUSTUP_HOME = $rustupHome
    $env:RUSTUP_TOOLCHAIN = $rustToolchain
    $env:RUSTUP_DIST_SERVER = "https://static.rust-lang.org"
    $env:RUSTUP_UPDATE_ROOT = "https://static.rust-lang.org/rustup"
    $env:RUSTUP_NO_UPDATE_CHECK = "1"
    foreach ($name in $environmentNames | Where-Object {
            $_ -notmatch '^(CARGO_HOME|RUSTUP_HOME|RUSTUP_TOOLCHAIN|RUSTUP_DIST_SERVER|RUSTUP_UPDATE_ROOT|RUSTUP_NO_UPDATE_CHECK|PATH)$'
        }) {
        Remove-Item "Env:\$name" -ErrorAction SilentlyContinue
    }
    $env:PATH = (Join-Path $cargoHome "bin") + ";" + $savedEnvironment["PATH"]

    if (-not (Test-Path -LiteralPath $rustupExe -PathType Leaf)) {
        Invoke-Checked -FilePath $rustupInit -Description "Pinned rustup install" `
            -Arguments @("-y", "--no-modify-path", "--profile", "minimal", "--default-toolchain", "none")
    }
    if ((Get-Sha256Lower -Path $rustupExe) -cne
        ([string]$lock.rustup.sha256).ToLowerInvariant()) {
        throw "Installed rustup does not match the pinned executable"
    }
    [Environment]::SetEnvironmentVariable("RUSTUP_TOOLCHAIN", $null)
    try {
        $observedRustupVersion = (& $rustupExe --version | Out-String).Trim()
        $rustupVersionExitCode = $LASTEXITCODE
    }
    finally {
        $env:RUSTUP_TOOLCHAIN = $rustToolchain
    }
    if ($rustupVersionExitCode -ne 0 -or
        $observedRustupVersion -notmatch (
            '^rustup ' + [regex]::Escape([string]$lock.rustup.version) +
            '(?:\s|$)')) {
        throw "Unexpected rustup version: $observedRustupVersion"
    }
    Invoke-Checked -FilePath $rustupExe -Description "Rustup profile selection" `
        -Arguments @("set", "profile", "minimal")
    if (-not (Test-Path -LiteralPath $rustcExe -PathType Leaf)) {
        Invoke-Checked -FilePath $rustupExe -Description "Pinned Rust install" `
            -Arguments @("toolchain", "install", $rustToolchain, "--profile", "minimal")
    }
    $expectedRustVersion = ($rustToolchain -split '-', 2)[0]
    $observedRustVersion = (& $rustcExe --version | Out-String).Trim()
    if ($LASTEXITCODE -ne 0 -or
        $observedRustVersion -notmatch ('^rustc ' + [regex]::Escape($expectedRustVersion) + '(?:\s|$)')) {
        throw "Unexpected Rust compiler: $observedRustVersion"
    }

    Write-Host "Development check: $Target"
    Invoke-Checked -FilePath $verusExe -Description "Verus target check" `
        -Arguments @($sourcePath, "--crate-type", "lib", "--no-cheating")
    if ((Get-Sha256Lower -Path $sourcePath) -cne $sourceHash) {
        throw "Target changed during verification: $Target"
    }
}
finally {
    foreach ($name in $environmentNames) {
        [Environment]::SetEnvironmentVariable($name, $savedEnvironment[$name])
    }
    if ($mutexHeld) {
        $mutex.ReleaseMutex()
    }
    $mutex.Dispose()
    if (Test-Path -LiteralPath $runRoot) {
        Remove-Item -Recurse -Force -LiteralPath $runRoot
    }
}
