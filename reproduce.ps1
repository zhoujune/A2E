[CmdletBinding()]
param(
    [ValidateSet("smoke", "full")]
    [string]$Suite = "smoke",
    [string]$OutputDirectory = "",
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
if ($DryRun) { $arguments += "--dry-run" }
if ($SkipVerus) { $arguments += "--skip-verus" }
if ($SkipRust) { $arguments += "--skip-rust" }
python "$root\artifact\reproduce.py" @arguments
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
