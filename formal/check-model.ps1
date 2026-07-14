[CmdletBinding()]
param(
    [ValidateSet("smoke", "full")]
    [string]$Suite = "full",

    [ValidateRange(1, 32)]
    [int]$Workers = 1,

    [string]$Scenario,

    [switch]$Coverage,

    [switch]$KeepStates,

    [string]$ResultsPath
)

$ErrorActionPreference = "Stop"

$toolDirectory = Join-Path $env:TEMP "proveai-tla-tools"
$jreVersion = "21.0.11+10"
$jreUri = "https://api.adoptium.net/v3/binary/version/jdk-21.0.11%2B10/windows/x64/jre/hotspot/normal/eclipse"
$jreSha256 = "BE26677AAA20B39A62EDCAAB4C8857A8B76673B0F45ABC0B6143B142B62717E4"
$tlaToolsVersion = "v1.7.4"
$tlaToolsUri = "https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar"
$tlaToolsSha256 = "936A262061C914694DFD669A543BE24573C45D5AA0FF20A8B96B23D01E050E88"

$jreArchive = Join-Path $toolDirectory "jre.zip"
$jreDirectory = Join-Path $toolDirectory "jre"
$jreVersionFile = Join-Path $jreDirectory "PROVEAI_JRE_VERSION"
$tlaTools = Join-Path $toolDirectory "tla2tools.jar"
$runId = [Guid]::NewGuid().ToString("N")
$stateDirectory = Join-Path $toolDirectory "states-$runId"
$invocationDirectory = (Get-Location).Path
$resolvedResultsPath = if ($ResultsPath) {
    if ([IO.Path]::IsPathRooted($ResultsPath)) {
        [IO.Path]::GetFullPath($ResultsPath)
    }
    else {
        [IO.Path]::GetFullPath((Join-Path $invocationDirectory $ResultsPath))
    }
}
else {
    $null
}

function Assert-TemporaryChildPath {
    param([Parameter(Mandatory = $true)][string]$Path)

    $temporaryRoot = [IO.Path]::GetFullPath($env:TEMP).TrimEnd('\') + '\'
    $resolved = [IO.Path]::GetFullPath($Path)
    if (-not $resolved.StartsWith(
            $temporaryRoot,
            [StringComparison]::OrdinalIgnoreCase)) {
        throw "Refusing filesystem operation outside the temporary directory: $resolved"
    }
}

function Get-VerifiedDownload {
    param(
        [Parameter(Mandatory = $true)][string]$Path,
        [Parameter(Mandatory = $true)][string]$Uri,
        [Parameter(Mandatory = $true)][string]$Sha256
    )

    if (Test-Path $Path) {
        $existingHash = (Get-FileHash -Algorithm SHA256 $Path).Hash
        if ($existingHash -eq $Sha256) {
            return
        }
        Remove-Item -LiteralPath $Path -Force
    }

    $partialPath = "$Path.$PID.download"
    Remove-Item -LiteralPath $partialPath -Force -ErrorAction SilentlyContinue
    Invoke-WebRequest -Uri $Uri -OutFile $partialPath

    $downloadedHash = (Get-FileHash -Algorithm SHA256 $partialPath).Hash
    if ($downloadedHash -ne $Sha256) {
        Remove-Item -LiteralPath $partialPath -Force
        throw "SHA-256 mismatch for $Uri. Expected $Sha256, got $downloadedHash."
    }

    Move-Item -LiteralPath $partialPath -Destination $Path
}

function ConvertFrom-TlcNumber {
    param([string]$Value)

    if ([string]::IsNullOrWhiteSpace($Value)) {
        return $null
    }
    return [Int64]::Parse(
        $Value.Replace(",", ""),
        [Globalization.CultureInfo]::InvariantCulture)
}

function Get-TlcMetrics {
    param(
        [Parameter(Mandatory = $true)]
        [AllowEmptyString()]
        [string]$Output
    )

    $fingerprintIndex = $null
    $seed = $null
    $aril = $null
    $generatedStates = $null
    $distinctStates = $null
    $depth = $null
    $tlcVersion = $null

    $versionMatch = [regex]::Match(
        $Output,
        '(?im)^TLC2 Version\s+(?<version>[^\r\n]+)')
    if ($versionMatch.Success) {
        $tlcVersion = $versionMatch.Groups["version"].Value.Trim()
    }

    $runMatch = [regex]::Match(
        $Output,
        '(?im)\bfp\s+(?<fingerprint>\d+)\s+and\s+seed\s+(?<seed>-?\d+)')
    if ($runMatch.Success) {
        $fingerprintIndex = ConvertFrom-TlcNumber `
            $runMatch.Groups["fingerprint"].Value
        $seed = ConvertFrom-TlcNumber $runMatch.Groups["seed"].Value
    }
    else {
        $fingerprintMatch = [regex]::Match(
            $Output,
            '(?im)\bfp\s+(?<fingerprint>\d+)')
        if ($fingerprintMatch.Success) {
            $fingerprintIndex = ConvertFrom-TlcNumber `
                $fingerprintMatch.Groups["fingerprint"].Value
        }
        $seedMatch = [regex]::Match($Output, '(?im)\bseed\s+(?<seed>-?\d+)')
        if ($seedMatch.Success) {
            $seed = ConvertFrom-TlcNumber $seedMatch.Groups["seed"].Value
        }
    }

    $arilMatch = [regex]::Match($Output, '(?im)\baril\s+(?<aril>-?\d+)')
    if ($arilMatch.Success) {
        $aril = ConvertFrom-TlcNumber $arilMatch.Groups["aril"].Value
    }

    $statisticsMatches = [regex]::Matches(
        $Output,
        '(?im)(?<generated>[\d,]+)\s+states?\s+generated,\s+' +
            '(?<distinct>[\d,]+)\s+distinct states? found')
    if ($statisticsMatches.Count -eq 0) {
        $statisticsMatches = [regex]::Matches(
            $Output,
            '(?im)Generated\s+(?<generated>[\d,]+)\s+states?,\s+' +
                '(?<distinct>[\d,]+)\s+distinct states? found')
    }
    if ($statisticsMatches.Count -gt 0) {
        $statisticsMatch = $statisticsMatches[$statisticsMatches.Count - 1]
        $generatedStates = ConvertFrom-TlcNumber `
            $statisticsMatch.Groups["generated"].Value
        $distinctStates = ConvertFrom-TlcNumber `
            $statisticsMatch.Groups["distinct"].Value
    }

    $depthMatch = [regex]::Match(
        $Output,
        '(?im)The depth of the complete state graph search is\s+(?<depth>[\d,]+)')
    if ($depthMatch.Success) {
        $depth = ConvertFrom-TlcNumber $depthMatch.Groups["depth"].Value
    }

    return [pscustomobject][ordered]@{
        tlcVersion = $tlcVersion
        fingerprintIndex = $fingerprintIndex
        seed = $seed
        aril = $aril
        generatedStates = $generatedStates
        distinctStates = $distinctStates
        depth = $depth
    }
}

function Write-ResultArtifact {
    param(
        [Parameter(Mandatory = $true)][string]$Path,
        [Parameter(Mandatory = $true)]$Document
    )

    $parentDirectory = Split-Path -Parent $Path
    New-Item -ItemType Directory -Force -Path $parentDirectory | Out-Null
    $temporaryPath = Join-Path $parentDirectory (
        ".{0}.{1}.{2}.tmp" -f `
            (Split-Path -Leaf $Path),
            $PID,
            [Guid]::NewGuid().ToString("N"))
    try {
        $json = $Document | ConvertTo-Json -Depth 10
        [IO.File]::WriteAllText(
            $temporaryPath,
            $json + [Environment]::NewLine,
            [Text.UTF8Encoding]::new($false))
        Move-Item -LiteralPath $temporaryPath -Destination $Path -Force
    }
    finally {
        Remove-Item -LiteralPath $temporaryPath -Force `
            -ErrorAction SilentlyContinue
    }
}

Assert-TemporaryChildPath -Path $toolDirectory

if ([System.Environment]::OSVersion.Platform -ne
        [System.PlatformID]::Win32NT -or
    -not [System.Environment]::Is64BitOperatingSystem -or
    [System.Runtime.InteropServices.RuntimeInformation]::OSArchitecture -ne
        [System.Runtime.InteropServices.Architecture]::X64) {
    throw "The bundled bootstrap requires a Windows x64 host."
}

New-Item -ItemType Directory -Force -Path $toolDirectory | Out-Null

$cacheMutex = [Threading.Mutex]::new($false, "ProveAI-TlaTools-Cache-v1")
$hasCacheLock = $false
try {
    $hasCacheLock = $cacheMutex.WaitOne([TimeSpan]::FromMinutes(5))
    if (-not $hasCacheLock) {
        throw "Timed out waiting for the model-checker cache lock."
    }

    Get-VerifiedDownload -Path $jreArchive -Uri $jreUri -Sha256 $jreSha256
    Get-VerifiedDownload -Path $tlaTools -Uri $tlaToolsUri -Sha256 $tlaToolsSha256

    $java = Join-Path $jreDirectory "bin\java.exe"
    $installedVersion = if (Test-Path $jreVersionFile) {
        (Get-Content -Raw $jreVersionFile).Trim()
    }
    else {
        ""
    }

    if ($installedVersion -ne $jreVersion -or -not (Test-Path $java)) {
        Assert-TemporaryChildPath -Path $jreDirectory
        Remove-Item -LiteralPath $jreDirectory -Recurse -Force `
            -ErrorAction SilentlyContinue
        $extractDirectory = Join-Path $toolDirectory "jre-extract-$PID"
        Assert-TemporaryChildPath -Path $extractDirectory
        Remove-Item -LiteralPath $extractDirectory -Recurse -Force `
            -ErrorAction SilentlyContinue
        Expand-Archive -LiteralPath $jreArchive -DestinationPath $extractDirectory
        $extractedJre = Get-ChildItem -Directory $extractDirectory |
            Select-Object -First 1
        if ($null -eq $extractedJre) {
            throw "The JRE archive did not contain a top-level directory."
        }
        Move-Item -LiteralPath $extractedJre.FullName -Destination $jreDirectory
        Set-Content -LiteralPath $jreVersionFile -Value $jreVersion -NoNewline
        Remove-Item -LiteralPath $extractDirectory -Recurse -Force
    }
}
finally {
    if ($hasCacheLock) {
        $cacheMutex.ReleaseMutex()
    }
    $cacheMutex.Dispose()
}

Assert-TemporaryChildPath -Path $stateDirectory
New-Item -ItemType Directory -Force -Path $stateDirectory | Out-Null

$formalDirectory = Split-Path -Parent $MyInvocation.MyCommand.Path
$java = Join-Path $jreDirectory "bin\java.exe"
$javaVersionPath = Join-Path $stateDirectory "java-version.txt"
$javaVersionProcess = Start-Process `
    -FilePath $java `
    -ArgumentList "-version" `
    -RedirectStandardError $javaVersionPath `
    -WindowStyle Hidden `
    -Wait `
    -PassThru
if ($javaVersionProcess.ExitCode -ne 0) {
    throw "The pinned Java runtime failed with exit code $($javaVersionProcess.ExitCode)."
}
$javaVersion = Get-Content -Raw $javaVersionPath
if ($javaVersion -notmatch [regex]::Escape("21.0.11")) {
    throw "Unexpected Java runtime version: $javaVersion"
}

$suitePath = Join-Path $formalDirectory "model-suite.json"
$resultSchemaPath = Join-Path $formalDirectory "results\schema.json"
$scenarios = (Get-Content -Raw $suitePath | ConvertFrom-Json).scenarios
if ($Scenario) {
    $scenarios = @($scenarios | Where-Object name -eq $Scenario)
    if ($scenarios.Count -eq 0) {
        throw "Unknown model-check scenario: $Scenario"
    }
}
elseif ($Suite -eq "smoke") {
    $scenarios = @($scenarios | Where-Object tier -eq "smoke")
}

$modelInputs = if ($resolvedResultsPath) {
    @(
        Get-ChildItem -LiteralPath $formalDirectory -Filter "*.tla" -File |
            Sort-Object Name |
            ForEach-Object {
                [pscustomobject][ordered]@{
                    path = $_.Name
                    sha256 = (Get-FileHash `
                        -Algorithm SHA256 `
                        -LiteralPath $_.FullName).Hash.ToLowerInvariant()
                }
            }
    )
}
else {
    @()
}
$resultScenarios = [Collections.Generic.List[object]]::new()
$resultDocument = if ($resolvedResultsPath) {
    [ordered]@{
        schemaVersion = "1.1.0"
        runId = $runId
        status = "running"
        startedAtUtc = [DateTimeOffset]::UtcNow.ToString("o")
        completedAtUtc = $null
        invocation = [ordered]@{
            workingDirectory = $invocationDirectory
            suite = if ($Scenario) { $null } else { $Suite }
            scenario = if ($Scenario) { $Scenario } else { $null }
            workers = $Workers
            coverage = [bool]$Coverage
        }
        manifest = [ordered]@{
            path = "model-suite.json"
            sha256 = (Get-FileHash -Algorithm SHA256 $suitePath).Hash.ToLowerInvariant()
        }
        runner = [ordered]@{
            path = "check-model.ps1"
            sha256 = (Get-FileHash -Algorithm SHA256 $PSCommandPath).Hash.ToLowerInvariant()
        }
        resultSchema = [ordered]@{
            path = "results/schema.json"
            sha256 = (Get-FileHash `
                -Algorithm SHA256 `
                -LiteralPath $resultSchemaPath).Hash.ToLowerInvariant()
        }
        modelInputs = $modelInputs
        scenarios = $resultScenarios
    }
}
else {
    $null
}
if ($resultDocument) {
    Write-ResultArtifact -Path $resolvedResultsPath -Document $resultDocument
}

$runSucceeded = $false

Push-Location $formalDirectory
try {
    foreach ($scenarioEntry in $scenarios) {
        $configuration = [string]$scenarioEntry.config
        $module = [string]$scenarioEntry.module
        if (-not (Test-Path $configuration) -or -not (Test-Path $module)) {
            throw "Scenario '$($scenarioEntry.name)' references a missing module or configuration."
        }
        $moduleSha256 = (Get-FileHash `
            -Algorithm SHA256 `
            -LiteralPath $module).Hash.ToLowerInvariant()
        $configurationSha256 = (Get-FileHash `
            -Algorithm SHA256 `
            -LiteralPath $configuration).Hash.ToLowerInvariant()

        $configurationStates = Join-Path `
            $stateDirectory `
            ([string]$scenarioEntry.name)
        New-Item -ItemType Directory -Force -Path $configurationStates |
            Out-Null

        Write-Host "Checking $($scenarioEntry.name) with TLA+ Tools $tlaToolsVersion"
        $tlcArguments = @(
            "-XX:+UseParallelGC",
            "-cp", $tlaTools,
            "tlc2.TLC",
            "-workers", $Workers
        )
        if ($Coverage) {
            $tlcArguments += @("-coverage", "9999")
        }
        $tlcArguments += @(
            "-metadir", $configurationStates,
            "-config", $configuration,
            $module
        )

        $scenarioStartedAt = [DateTimeOffset]::UtcNow
        $scenarioTimer = [Diagnostics.Stopwatch]::StartNew()
        $scenarioExitStatus = $null
        $scenarioInvocationError = $null
        $tlcOutputPath = Join-Path $configurationStates "tlc-output.txt"
        try {
            if ($resolvedResultsPath) {
                & $java @tlcArguments |
                    Tee-Object -FilePath $tlcOutputPath |
                    Out-Host
                $scenarioExitStatus = $LASTEXITCODE
            }
            else {
                & $java @tlcArguments
                $scenarioExitStatus = $LASTEXITCODE
            }
        }
        catch {
            $scenarioInvocationError = $_
        }
        finally {
            $scenarioTimer.Stop()
        }
        $scenarioCompletedAt = [DateTimeOffset]::UtcNow

        if ($resultDocument) {
            $tlcOutput = if (Test-Path $tlcOutputPath) {
                Get-Content -Raw $tlcOutputPath
            }
            else {
                ""
            }
            $metrics = Get-TlcMetrics -Output $tlcOutput
            $scenarioResult = [pscustomobject][ordered]@{
                name = [string]$scenarioEntry.name
                tier = [string]$scenarioEntry.tier
                status = if (
                    $null -eq $scenarioInvocationError -and
                    $scenarioExitStatus -eq 0) {
                    "passed"
                }
                else {
                    "failed"
                }
                startedAtUtc = $scenarioStartedAt.ToString("o")
                completedAtUtc = $scenarioCompletedAt.ToString("o")
                durationMilliseconds = [Int64][Math]::Round(
                    $scenarioTimer.Elapsed.TotalMilliseconds)
                exitStatus = $scenarioExitStatus
                error = if ($scenarioInvocationError) {
                    $scenarioInvocationError.Exception.Message
                }
                else {
                    $null
                }
                workers = $Workers
                coverage = [bool]$Coverage
                module = [ordered]@{
                    path = $module
                    sha256 = $moduleSha256
                }
                configuration = [ordered]@{
                    path = $configuration
                    sha256 = $configurationSha256
                }
                toolchain = [ordered]@{
                    tlaToolsVersion = $tlaToolsVersion
                    tlaToolsSha256 = $tlaToolsSha256.ToLowerInvariant()
                    observedTlcVersion = $metrics.tlcVersion
                    jreVersion = $jreVersion
                    jreSha256 = $jreSha256.ToLowerInvariant()
                    observedJavaVersion = $javaVersion.Trim()
                }
                exploration = [ordered]@{
                    fingerprintIndex = $metrics.fingerprintIndex
                    seed = $metrics.seed
                    aril = $metrics.aril
                }
                statistics = [ordered]@{
                    generatedStates = $metrics.generatedStates
                    distinctStates = $metrics.distinctStates
                    depth = $metrics.depth
                }
            }
            $resultScenarios.Add($scenarioResult)
            Write-ResultArtifact `
                -Path $resolvedResultsPath `
                -Document $resultDocument
        }

        if ($scenarioInvocationError) {
            throw $scenarioInvocationError
        }
        if ($scenarioExitStatus -ne 0) {
            throw "Scenario '$($scenarioEntry.name)' failed with exit code $scenarioExitStatus."
        }
    }
    $runSucceeded = $true
}
finally {
    Pop-Location
    if ($resultDocument) {
        $resultDocument.status = if ($runSucceeded) { "passed" } else { "failed" }
        $resultDocument.completedAtUtc = [DateTimeOffset]::UtcNow.ToString("o")
        Write-ResultArtifact `
            -Path $resolvedResultsPath `
            -Document $resultDocument
    }
    if ($runSucceeded -and -not $KeepStates) {
        Assert-TemporaryChildPath -Path $stateDirectory
        Remove-Item -LiteralPath $stateDirectory -Recurse -Force
    }
    elseif (Test-Path $stateDirectory) {
        Write-Host "TLC state retained at $stateDirectory"
    }
}
