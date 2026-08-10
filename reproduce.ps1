[CmdletBinding()]
param(
    [ValidateSet("smoke", "full")]
    [string]$Suite = "smoke",
    [string]$OutputDirectory = "",
    [int]$Workers = 1,
    [double]$TimeoutSeconds = 3600,
    [string]$OfflineBundleRoot = "",
    [switch]$DryRun,
    [switch]$SkipVerus,
    [switch]$SkipRust
)

$ErrorActionPreference = "Stop"
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
$arguments = @($Suite, "--repository", $root)
if (-not [string]::IsNullOrWhiteSpace($OutputDirectory)) {
    $arguments += @("--output-directory", $OutputDirectory)
}
$arguments += @("--workers", $Workers, "--timeout-seconds", $TimeoutSeconds)
if ($DryRun) { $arguments += "--dry-run" }
if ($SkipVerus) { $arguments += "--skip-verus" }
if ($SkipRust) { $arguments += "--skip-rust" }
if (-not [string]::IsNullOrWhiteSpace($OfflineBundleRoot)) {
    $arguments += @("--offline-bundle-root", $OfflineBundleRoot)
}
python "$root\artifact\reproduce.py" @arguments
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
