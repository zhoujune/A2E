[CmdletBinding()]
param(
    [ValidateSet("smoke", "full")]
    [string]$Suite = "full",

    [ValidateRange(1, 32)]
    [int]$Workers = 1,

    [string]$Scenario,

    [switch]$Coverage,

    [switch]$KeepStates,

    [string]$ResultsPath,

    [switch]$NoResults
)

$ErrorActionPreference = "Stop"

$toolDirectory = Join-Path $env:TEMP "proveai-tla-tools"
$jreVersion = "21.0.11+10"
$jreUri = "https://api.adoptium.net/v3/binary/version/jdk-21.0.11%2B10/windows/x64/jre/hotspot/normal/eclipse"
$jreSha256 = "BE26677AAA20B39A62EDCAAB4C8857A8B76673B0F45ABC0B6143B142B62717E4"
$tlaToolsVersion = "v1.7.4"
$tlaToolsUri = "https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar"
$tlaToolsSha256 = "936A262061C914694DFD669A543BE24573C45D5AA0FF20A8B96B23D01E050E88"

$cachedJreArchive = Join-Path $toolDirectory "jre.zip"
$cachedTlaTools = Join-Path $toolDirectory "tla2tools.jar"
$runId = [Guid]::NewGuid().ToString("N")
$stateDirectory = Join-Path $toolDirectory "states-$runId"
$snapshotDirectory = Join-Path $stateDirectory "model-snapshot"
$runToolDirectory = Join-Path $stateDirectory "toolchain"
$javaTemporaryDirectory = Join-Path $stateDirectory "java-temp"
$runJreArchive = Join-Path $runToolDirectory "jre.zip"
$jreDirectory = Join-Path $runToolDirectory "jre"
$tlaTools = Join-Path $runToolDirectory "tla2tools.jar"
$invocationDirectory = (Get-Location).Path
$formalDirectory = Split-Path -Parent $MyInvocation.MyCommand.Path
$repositoryDirectory = Split-Path -Parent $formalDirectory
$suitePath = Join-Path $formalDirectory "model-suite.json"
$resultSchemaPath = Join-Path $formalDirectory "results\schema.json"

if ($NoResults -and $ResultsPath) {
    throw "-NoResults and -ResultsPath cannot be used together."
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

    $current = $temporaryRoot.TrimEnd('\')
    $relative = $resolved.Substring($temporaryRoot.Length)
    foreach ($component in @($relative -split '\\' | Where-Object { $_ })) {
        $current = Join-Path $current $component
        if (Test-Path -LiteralPath $current) {
            $item = Get-Item -Force -LiteralPath $current
            if (($item.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) {
                throw "Refusing a temporary path through a reparse point: $current"
            }
        }
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
    Invoke-WebRequest -UseBasicParsing -Uri $Uri -OutFile $partialPath

    $downloadedHash = (Get-FileHash -Algorithm SHA256 $partialPath).Hash
    if ($downloadedHash -ne $Sha256) {
        Remove-Item -LiteralPath $partialPath -Force
        throw "SHA-256 mismatch for $Uri. Expected $Sha256, got $downloadedHash."
    }

    Move-Item -LiteralPath $partialPath -Destination $Path
}

function Get-Sha256ForBytes {
    param([Parameter(Mandatory = $true)][byte[]]$Bytes)

    $algorithm = [Security.Cryptography.SHA256]::Create()
    try {
        $digest = $algorithm.ComputeHash($Bytes)
        return ([BitConverter]::ToString($digest)).Replace("-", "").ToLowerInvariant()
    }
    finally {
        $algorithm.Dispose()
    }
}

function Get-SanitizedRepositoryRelativePath {
    param(
        [Parameter(Mandatory = $true)][string]$Path,
        [Parameter(Mandatory = $true)][string]$RepositoryDirectory
    )

    $resolvedPath = [IO.Path]::GetFullPath($Path).TrimEnd('\')
    $resolvedRepository = [IO.Path]::GetFullPath($RepositoryDirectory).TrimEnd('\')
    if ($resolvedPath.Equals(
            $resolvedRepository,
            [StringComparison]::OrdinalIgnoreCase)) {
        return "."
    }

    $repositoryPrefix = $resolvedRepository + '\'
    if ($resolvedPath.StartsWith(
            $repositoryPrefix,
            [StringComparison]::OrdinalIgnoreCase)) {
        return $resolvedPath.Substring($repositoryPrefix.Length).Replace('\', '/')
    }

    return "<outside-repository>"
}

function Get-DirectoryInventory {
    param([Parameter(Mandatory = $true)][string]$Directory)

    $resolvedDirectory = [IO.Path]::GetFullPath($Directory).TrimEnd('\')
    $entries = [Collections.Generic.List[object]]::new()
    foreach ($item in @(
            Get-ChildItem -LiteralPath $resolvedDirectory -Force -Recurse |
                Sort-Object FullName)) {
        if (($item.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) {
            throw "Reparse points are not allowed in an execution snapshot: $($item.FullName)"
        }

        $relativePath = $item.FullName.Substring(
            $resolvedDirectory.Length).TrimStart('\').Replace('\', '/')
        if ($relativePath.Contains("`t") -or
            $relativePath.Contains("`r") -or
            $relativePath.Contains("`n")) {
            throw "Execution-snapshot paths cannot contain control separators."
        }

        if ($item.PSIsContainer) {
            $entries.Add([pscustomobject][ordered]@{
                    path = $relativePath
                    kind = "directory"
                    sha256 = $null
                })
        }
        else {
            $entries.Add([pscustomobject][ordered]@{
                    path = $relativePath
                    kind = "file"
                    sha256 = (Get-FileHash `
                        -Algorithm SHA256 `
                        -LiteralPath $item.FullName).Hash.ToLowerInvariant()
                })
        }
    }

    if ($entries.Count -eq 0) {
        throw "Execution snapshot is empty: $resolvedDirectory"
    }

    $digestLines = foreach ($entry in $entries) {
        if ($entry.kind -eq "directory") {
            "D`t$($entry.path)"
        }
        else {
            "F`t$($entry.path)`t$($entry.sha256)"
        }
    }
    $digestText = ($digestLines -join "`n") + "`n"
    $digestBytes = [Text.UTF8Encoding]::new($false).GetBytes($digestText)

    return [pscustomobject][ordered]@{
        entries = @($entries)
        fileCount = @($entries | Where-Object kind -eq "file").Count
        directoryCount = @($entries | Where-Object kind -eq "directory").Count
        treeSha256 = Get-Sha256ForBytes -Bytes $digestBytes
    }
}

function Assert-DirectoryIntegrity {
    param(
        [Parameter(Mandatory = $true)][string]$Directory,
        [Parameter(Mandatory = $true)]$ExpectedInventory,
        [Parameter(Mandatory = $true)][string]$Description
    )

    $actual = Get-DirectoryInventory -Directory $Directory
    $expectedEntries = @($ExpectedInventory.entries)
    $actualEntries = @($actual.entries)
    if ($actualEntries.Count -ne $expectedEntries.Count) {
        throw "$Description membership changed during execution. Expected $($expectedEntries.Count) entries, found $($actualEntries.Count)."
    }

    for ($index = 0; $index -lt $expectedEntries.Count; $index++) {
        $expected = $expectedEntries[$index]
        $observed = $actualEntries[$index]
        if ([string]$observed.path -cne [string]$expected.path -or
            [string]$observed.kind -cne [string]$expected.kind) {
            throw "$Description membership changed during execution at entry $index."
        }
        if ($expected.kind -eq "file" -and
            [string]$observed.sha256 -cne [string]$expected.sha256) {
            throw "$Description file changed during execution: $($expected.path)."
        }
    }

    if ([string]$actual.treeSha256 -cne [string]$ExpectedInventory.treeSha256) {
        throw "$Description aggregate digest changed during execution."
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
            throw "$Description disappeared during execution: $path"
        }
        $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $path).
            Hash.ToLowerInvariant()
        if ($actual -cne [string]$input.sha256) {
            throw "$Description changed during execution: $path"
        }
    }
}

function Read-Manifest {
    param([Parameter(Mandatory = $true)][string]$Path)

    $bytes = [IO.File]::ReadAllBytes($Path)
    $offset = 0
    if ($bytes.Length -ge 3 -and
        $bytes[0] -eq 0xEF -and
        $bytes[1] -eq 0xBB -and
        $bytes[2] -eq 0xBF) {
        $offset = 3
    }
    $encoding = [Text.UTF8Encoding]::new($false, $true)
    $json = $encoding.GetString($bytes, $offset, $bytes.Length - $offset)
    try {
        $manifest = $json | ConvertFrom-Json
    }
    catch {
        throw "Invalid model-suite.json: $($_.Exception.Message)"
    }

    return [pscustomobject][ordered]@{
        document = $manifest
        sha256 = Get-Sha256ForBytes -Bytes $bytes
    }
}

function Assert-ExactProperties {
    param(
        [Parameter(Mandatory = $true)]$Object,
        [Parameter(Mandatory = $true)][string[]]$Required,
        [Parameter(Mandatory = $true)][string]$Description
    )

    if ($null -eq $Object -or $Object -isnot [pscustomobject]) {
        throw "$Description must be a JSON object."
    }
    $actual = @($Object.PSObject.Properties.Name)
    $missing = @($Required | Where-Object { $actual -cnotcontains $_ })
    $unexpected = @($actual | Where-Object { $Required -cnotcontains $_ })
    if ($missing.Count -gt 0) {
        throw "$Description is missing required properties: $($missing -join ', ')."
    }
    if ($unexpected.Count -gt 0) {
        throw "$Description has unexpected properties: $($unexpected -join ', ')."
    }
}

function Assert-LeafInputName {
    param(
        [Parameter(Mandatory = $true)][string]$Name,
        [Parameter(Mandatory = $true)][string]$Extension,
        [Parameter(Mandatory = $true)][string]$Description
    )

    if ([string]::IsNullOrWhiteSpace($Name) -or
        [IO.Path]::IsPathRooted($Name) -or
        $Name.Contains("\") -or
        $Name.Contains("/") -or
        [IO.Path]::GetFileName($Name) -cne $Name -or
        [IO.Path]::GetExtension($Name) -cne $Extension) {
        throw "$Description must be a local $Extension leaf filename, got '$Name'."
    }
}

function Assert-Manifest {
    param(
        [Parameter(Mandatory = $true)]$Manifest,
        [Parameter(Mandatory = $true)][string]$FormalDirectory
    )

    Assert-ExactProperties `
        -Object $Manifest `
        -Required @("scenarios") `
        -Description "model-suite.json"

    $entries = @($Manifest.scenarios)
    if ($entries.Count -eq 0) {
        throw "model-suite.json must declare at least one scenario."
    }

    $names = [Collections.Generic.HashSet[string]]::new(
        [StringComparer]::OrdinalIgnoreCase)
    $configurations = [Collections.Generic.HashSet[string]]::new(
        [StringComparer]::OrdinalIgnoreCase)
    $tierCounts = @{ smoke = 0; full = 0 }

    foreach ($entry in $entries) {
        Assert-ExactProperties `
            -Object $entry `
            -Required @("name", "tier", "module", "config") `
            -Description "model-suite.json scenario entry"

        $name = [string]$entry.name
        $tier = [string]$entry.tier
        $module = [string]$entry.module
        $configuration = [string]$entry.config

        if ($name -cnotmatch '^[a-z0-9][a-z0-9-]*$') {
            throw "Scenario name '$name' must use lowercase letters, digits, and hyphens."
        }
        if (-not $names.Add($name)) {
            throw "Duplicate scenario name in model-suite.json: '$name'."
        }
        if (@("smoke", "full") -cnotcontains $tier) {
            throw "Scenario '$name' has invalid tier '$tier'; expected 'smoke' or 'full'."
        }
        $tierCounts[$tier]++

        Assert-LeafInputName `
            -Name $module `
            -Extension ".tla" `
            -Description "Scenario '$name' module"
        Assert-LeafInputName `
            -Name $configuration `
            -Extension ".cfg" `
            -Description "Scenario '$name' configuration"
        if (-not $configurations.Add($configuration)) {
            throw "Configuration '$configuration' is registered by more than one scenario."
        }

        $modulePath = Join-Path $FormalDirectory $module
        $configurationPath = Join-Path $FormalDirectory $configuration
        if (-not (Test-Path -LiteralPath $modulePath -PathType Leaf) -or
            -not (Test-Path -LiteralPath $configurationPath -PathType Leaf)) {
            throw "Scenario '$name' references a missing module or configuration."
        }
    }

    if ($tierCounts.smoke -eq 0 -or $tierCounts.full -eq 0) {
        throw "model-suite.json must contain at least one smoke and one full-tier scenario."
    }

    $unregistered = @(
        Get-ChildItem -LiteralPath $FormalDirectory -Filter "*.cfg" -File |
            Where-Object { -not $configurations.Contains($_.Name) } |
            Sort-Object Name |
            ForEach-Object Name
    )
    if ($unregistered.Count -gt 0) {
        throw "Unregistered formal configuration files: $($unregistered -join ', ')."
    }

    return $entries
}

function New-ModelSnapshot {
    param(
        [Parameter(Mandatory = $true)][string]$FormalDirectory,
        [Parameter(Mandatory = $true)][string]$SnapshotDirectory,
        [Parameter(Mandatory = $true)][object[]]$Scenarios
    )

    Assert-TemporaryChildPath -Path $SnapshotDirectory
    New-Item -ItemType Directory -Path $SnapshotDirectory | Out-Null

    $tlaFiles = @(
        Get-ChildItem -LiteralPath $FormalDirectory -Filter "*.tla" -File |
            Sort-Object Name
    )
    if ($tlaFiles.Count -eq 0) {
        throw "No local TLA+ modules were found in $FormalDirectory."
    }
    $configurationNames = @(
        $Scenarios |
            ForEach-Object { [string]$_.config } |
            Sort-Object -Unique
    )

    foreach ($source in $tlaFiles) {
        Copy-Item `
            -LiteralPath $source.FullName `
            -Destination (Join-Path $SnapshotDirectory $source.Name)
    }
    foreach ($name in $configurationNames) {
        Copy-Item `
            -LiteralPath (Join-Path $FormalDirectory $name) `
            -Destination (Join-Path $SnapshotDirectory $name)
    }

    $hashes = [Collections.Generic.Dictionary[string, string]]::new(
        [StringComparer]::OrdinalIgnoreCase)
    $expectedInputs = [Collections.Generic.List[object]]::new()
    foreach ($file in @(
            Get-ChildItem -LiteralPath $SnapshotDirectory -File |
                Sort-Object Name)) {
        $hash = (Get-FileHash -Algorithm SHA256 -LiteralPath $file.FullName).
            Hash.ToLowerInvariant()
        $hashes.Add($file.Name, $hash)
        $expectedInputs.Add([pscustomobject][ordered]@{
                path = $file.Name
                sha256 = $hash
            })
        $file.IsReadOnly = $true
    }

    $modelInputs = @(
        $expectedInputs |
            Where-Object { [IO.Path]::GetExtension($_.path) -ieq ".tla" }
    )
    return [pscustomobject][ordered]@{
        hashes = $hashes
        expectedInputs = @($expectedInputs)
        modelInputs = $modelInputs
        tlaFileCount = $tlaFiles.Count
        configurationFileCount = $configurationNames.Count
    }
}

function Assert-SnapshotIntegrity {
    param(
        [Parameter(Mandatory = $true)][string]$SnapshotDirectory,
        [Parameter(Mandatory = $true)][object[]]$ExpectedInputs
    )

    $expectedNames = [Collections.Generic.HashSet[string]]::new(
        [StringComparer]::OrdinalIgnoreCase)
    foreach ($input in $ExpectedInputs) {
        if (-not $expectedNames.Add([string]$input.path)) {
            throw "Frozen model input baseline contains a duplicate path: $($input.path)."
        }
    }

    $actualItems = @(
        Get-ChildItem -LiteralPath $SnapshotDirectory -Force |
            Sort-Object Name
    )
    $unexpectedItems = @(
        $actualItems |
            Where-Object {
                $_.PSIsContainer -or -not $expectedNames.Contains($_.Name)
            } |
            ForEach-Object Name
    )
    if ($unexpectedItems.Count -gt 0) {
        throw "Frozen model snapshot membership changed during execution: $($unexpectedItems -join ', ')."
    }
    if ($actualItems.Count -ne $expectedNames.Count) {
        throw "Frozen model snapshot membership changed during execution. Expected $($expectedNames.Count) files, found $($actualItems.Count)."
    }

    foreach ($input in $ExpectedInputs) {
        $path = Join-Path $SnapshotDirectory ([string]$input.path)
        if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
            throw "Frozen model input disappeared during execution: $($input.path)."
        }
        $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $path).
            Hash.ToLowerInvariant()
        if ($actual -cne [string]$input.sha256) {
            throw "Frozen model input changed during execution: $($input.path)."
        }
    }
}

function Assert-SelectedScenarioCompleteness {
    param(
        [Parameter(Mandatory = $true)][object[]]$SelectedScenarios,
        [Parameter(Mandatory = $true)][object[]]$CompletedScenarios,
        [Parameter(Mandatory = $true)][string]$Description
    )

    if ($SelectedScenarios.Count -eq 0) {
        throw "$Description cannot pass with an empty scenario selection."
    }
    if ($CompletedScenarios.Count -ne $SelectedScenarios.Count) {
        throw "$Description is incomplete. Expected $($SelectedScenarios.Count) scenarios, completed $($CompletedScenarios.Count)."
    }

    for ($index = 0; $index -lt $SelectedScenarios.Count; $index++) {
        $selected = $SelectedScenarios[$index]
        $completed = $CompletedScenarios[$index]
        $completedModule = if ($completed.module -is [string]) {
            [string]$completed.module
        }
        else {
            [string]$completed.module.path
        }
        $completedConfiguration = if ($completed.configuration -is [string]) {
            [string]$completed.configuration
        }
        else {
            [string]$completed.configuration.path
        }
        if ([string]$completed.name -cne [string]$selected.name -or
            [string]$completed.tier -cne [string]$selected.tier -or
            $completedModule -cne [string]$selected.module -or
            $completedConfiguration -cne [string]$selected.config) {
            throw "$Description does not match the selected scenario at index $index."
        }
        if ([string]$completed.status -cne "passed" -or
            $completed.exitStatus -ne 0 -or
            $null -ne $completed.error) {
            throw "$Description contains a non-passing scenario: $($selected.name)."
        }
    }
}

function Reserve-ResultArtifact {
    param([Parameter(Mandatory = $true)][string]$Path)

    $parentDirectory = Split-Path -Parent $Path
    New-Item -ItemType Directory -Force -Path $parentDirectory | Out-Null
    try {
        $stream = [IO.File]::Open(
            $Path,
            [IO.FileMode]::CreateNew,
            [IO.FileAccess]::Write,
            [IO.FileShare]::None)
        $stream.Dispose()
    }
    catch [IO.IOException] {
        throw "Refusing to overwrite an existing result artifact: $Path"
    }
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

$runnerHash = (Get-FileHash `
    -Algorithm SHA256 `
    -LiteralPath $PSCommandPath).Hash.ToLowerInvariant()
$resultSchemaHash = (Get-FileHash `
    -Algorithm SHA256 `
    -LiteralPath $resultSchemaPath).Hash.ToLowerInvariant()
$manifestData = Read-Manifest -Path $suitePath
$boundArtifactInputs = @(
    [pscustomobject]@{ path = $PSCommandPath; sha256 = $runnerHash },
    [pscustomobject]@{ path = $suitePath; sha256 = $manifestData.sha256 },
    [pscustomobject]@{ path = $resultSchemaPath; sha256 = $resultSchemaHash }
)
Assert-HashedFileIntegrity `
    -Inputs $boundArtifactInputs `
    -Description "Bound artifact input"
$allScenarios = @(
    Assert-Manifest `
        -Manifest $manifestData.document `
        -FormalDirectory $formalDirectory
)
if ($Scenario) {
    $scenarios = @($allScenarios | Where-Object name -eq $Scenario)
    if ($scenarios.Count -eq 0) {
        throw "Unknown model-check scenario: $Scenario"
    }
}
elseif ($Suite -eq "smoke") {
    $scenarios = @($allScenarios | Where-Object tier -eq "smoke")
}
else {
    $scenarios = $allScenarios
}

$resolvedResultsPath = if ($NoResults) {
    $null
}
elseif ($ResultsPath) {
    if ([IO.Path]::IsPathRooted($ResultsPath)) {
        [IO.Path]::GetFullPath($ResultsPath)
    }
    else {
        [IO.Path]::GetFullPath((Join-Path $invocationDirectory $ResultsPath))
    }
}
else {
    $selectionName = if ($Scenario) {
        [string]$scenarios[0].name
    }
    else {
        $Suite
    }
    $resultName = "{0}-{1}-{2}.result.json" -f `
        [DateTimeOffset]::UtcNow.ToString("yyyyMMddTHHmmssfffZ"), `
        $selectionName, `
        $runId
    [IO.Path]::GetFullPath((Join-Path $formalDirectory "results\$resultName"))
}
if ($resolvedResultsPath -and (Test-Path -LiteralPath $resolvedResultsPath)) {
    throw "Refusing to overwrite an existing result artifact: $resolvedResultsPath"
}
$reportedWorkingDirectory = Get-SanitizedRepositoryRelativePath `
    -Path $invocationDirectory `
    -RepositoryDirectory $repositoryDirectory

Assert-TemporaryChildPath -Path $toolDirectory

if ([System.Environment]::OSVersion.Platform -ne
        [System.PlatformID]::Win32NT -or
    -not [System.Environment]::Is64BitOperatingSystem -or
    [System.Runtime.InteropServices.RuntimeInformation]::OSArchitecture -ne
        [System.Runtime.InteropServices.Architecture]::X64) {
    throw "The bundled bootstrap requires a Windows x64 host."
}

New-Item -ItemType Directory -Force -Path $toolDirectory | Out-Null
Assert-TemporaryChildPath -Path $stateDirectory
New-Item -ItemType Directory -Path $stateDirectory | Out-Null
New-Item -ItemType Directory -Path $runToolDirectory | Out-Null
New-Item -ItemType Directory -Path $javaTemporaryDirectory | Out-Null

$cacheMutex = [Threading.Mutex]::new($false, "ProveAI-TlaTools-Cache-v1")
$hasCacheLock = $false
try {
    $hasCacheLock = $cacheMutex.WaitOne([TimeSpan]::FromMinutes(5))
    if (-not $hasCacheLock) {
        throw "Timed out waiting for the model-checker cache lock."
    }

    Get-VerifiedDownload `
        -Path $cachedJreArchive `
        -Uri $jreUri `
        -Sha256 $jreSha256
    Get-VerifiedDownload `
        -Path $cachedTlaTools `
        -Uri $tlaToolsUri `
        -Sha256 $tlaToolsSha256

    Copy-Item -LiteralPath $cachedJreArchive -Destination $runJreArchive
    Copy-Item -LiteralPath $cachedTlaTools -Destination $tlaTools

    $runArchiveHash = (Get-FileHash `
        -Algorithm SHA256 `
        -LiteralPath $runJreArchive).Hash
    $runJarHash = (Get-FileHash `
        -Algorithm SHA256 `
        -LiteralPath $tlaTools).Hash
    if ($runArchiveHash -cne $jreSha256 -or
        $runJarHash -cne $tlaToolsSha256) {
        throw "A per-run tool copy does not match its validated cache artifact."
    }
}
finally {
    if ($hasCacheLock) {
        $cacheMutex.ReleaseMutex()
    }
    $cacheMutex.Dispose()
}

$extractDirectory = Join-Path $runToolDirectory "jre-extract"
New-Item -ItemType Directory -Path $extractDirectory | Out-Null
Expand-Archive `
    -LiteralPath $runJreArchive `
    -DestinationPath $extractDirectory
$extractedEntries = @(Get-ChildItem -LiteralPath $extractDirectory -Force)
if ($extractedEntries.Count -ne 1 -or -not $extractedEntries[0].PSIsContainer) {
    throw "The pinned JRE archive must contain exactly one top-level directory."
}
Move-Item `
    -LiteralPath $extractedEntries[0].FullName `
    -Destination $jreDirectory
Remove-Item -LiteralPath $extractDirectory -Force

$java = Join-Path $jreDirectory "bin\java.exe"
if (-not (Test-Path -LiteralPath $java -PathType Leaf)) {
    throw "The freshly extracted JRE does not contain bin\java.exe."
}

$runToolCreatedAt = [DateTimeOffset]::UtcNow
$runToolInventory = Get-DirectoryInventory -Directory $runToolDirectory
$runTlaToolsHash = (Get-FileHash `
    -Algorithm SHA256 `
    -LiteralPath $tlaTools).Hash.ToLowerInvariant()
$runJavaHash = (Get-FileHash `
    -Algorithm SHA256 `
    -LiteralPath $java).Hash.ToLowerInvariant()
if ($runTlaToolsHash -cne $tlaToolsSha256.ToLowerInvariant()) {
    throw "The per-run TLA+ Tools JAR changed before execution."
}

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
Assert-DirectoryIntegrity `
    -Directory $runToolDirectory `
    -ExpectedInventory $runToolInventory `
    -Description "Per-run tool snapshot"

$snapshotCreatedAt = [DateTimeOffset]::UtcNow
$snapshot = New-ModelSnapshot `
    -FormalDirectory $formalDirectory `
    -SnapshotDirectory $snapshotDirectory `
    -Scenarios $scenarios
Assert-SnapshotIntegrity `
    -SnapshotDirectory $snapshotDirectory `
    -ExpectedInputs $snapshot.expectedInputs

if ($resolvedResultsPath) {
    Reserve-ResultArtifact -Path $resolvedResultsPath
}

$resultScenarios = [Collections.Generic.List[object]]::new()
$completedScenarios = [Collections.Generic.List[object]]::new()
$resultDocument = if ($resolvedResultsPath) {
    [ordered]@{
        schemaVersion = "1.3.0"
        runId = $runId
        status = "running"
        startedAtUtc = [DateTimeOffset]::UtcNow.ToString("o")
        completedAtUtc = $null
        invocation = [ordered]@{
            workingDirectory = $reportedWorkingDirectory
            suite = if ($Scenario) { $null } else { $Suite }
            scenario = if ($Scenario) { $Scenario } else { $null }
            workers = $Workers
            coverage = [bool]$Coverage
        }
        manifest = [ordered]@{
            path = "model-suite.json"
            sha256 = $manifestData.sha256
        }
        runner = [ordered]@{
            path = "check-model.ps1"
            sha256 = $runnerHash
        }
        resultSchema = [ordered]@{
            path = "results/schema.json"
            sha256 = $resultSchemaHash
        }
        snapshot = [ordered]@{
            kind = "isolated-read-only-copy"
            createdAtUtc = $snapshotCreatedAt.ToString("o")
            tlaFileCount = $snapshot.tlaFileCount
            configurationFileCount = $snapshot.configurationFileCount
        }
        toolSnapshot = [ordered]@{
            kind = "isolated-per-run-copy"
            createdAtUtc = $runToolCreatedAt.ToString("o")
            fileCount = $runToolInventory.fileCount
            directoryCount = $runToolInventory.directoryCount
            treeSha256 = $runToolInventory.treeSha256
            jreArchive = [ordered]@{
                path = "jre.zip"
                sha256 = $runArchiveHash.ToLowerInvariant()
            }
            tlaTools = [ordered]@{
                path = "tla2tools.jar"
                sha256 = $runTlaToolsHash
            }
            java = [ordered]@{
                path = "jre/bin/java.exe"
                sha256 = $runJavaHash
            }
        }
        modelInputs = $snapshot.modelInputs
        scenarios = $resultScenarios
    }
}
else {
    $null
}
if ($resultDocument) {
    Write-ResultArtifact -Path $resolvedResultsPath -Document $resultDocument
    Write-Host "Result report: $resolvedResultsPath"
}

$runSucceeded = $false

Push-Location $snapshotDirectory
try {
    foreach ($scenarioEntry in $scenarios) {
        $configuration = [string]$scenarioEntry.config
        $module = [string]$scenarioEntry.module
        $moduleSha256 = $snapshot.hashes[$module]
        $configurationSha256 = $snapshot.hashes[$configuration]

        $configurationStates = Join-Path `
            $stateDirectory `
            ([string]$scenarioEntry.name)
        New-Item -ItemType Directory -Force -Path $configurationStates |
            Out-Null

        Write-Host "Checking $($scenarioEntry.name) with TLA+ Tools $tlaToolsVersion"
        $tlcArguments = @(
            "-XX:+UseParallelGC",
            "-Djava.io.tmpdir=$javaTemporaryDirectory",
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
        $scenarioIntegrityError = $null
        $tlcOutputPath = Join-Path $configurationStates "tlc-output.txt"
        try {
            Assert-HashedFileIntegrity `
                -Inputs $boundArtifactInputs `
                -Description "Bound artifact input"
            Assert-DirectoryIntegrity `
                -Directory $runToolDirectory `
                -ExpectedInventory $runToolInventory `
                -Description "Per-run tool snapshot"
            Assert-SnapshotIntegrity `
                -SnapshotDirectory $snapshotDirectory `
                -ExpectedInputs $snapshot.expectedInputs
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
            try {
                Assert-HashedFileIntegrity `
                    -Inputs $boundArtifactInputs `
                    -Description "Bound artifact input"
                Assert-DirectoryIntegrity `
                    -Directory $runToolDirectory `
                    -ExpectedInventory $runToolInventory `
                    -Description "Per-run tool snapshot"
                Assert-SnapshotIntegrity `
                    -SnapshotDirectory $snapshotDirectory `
                    -ExpectedInputs $snapshot.expectedInputs
            }
            catch {
                $scenarioIntegrityError = $_
            }
            $scenarioTimer.Stop()
        }
        $scenarioCompletedAt = [DateTimeOffset]::UtcNow
        $scenarioPassed = (
            $null -eq $scenarioInvocationError -and
            $null -eq $scenarioIntegrityError -and
            $scenarioExitStatus -eq 0)
        $scenarioErrorMessage = if ($scenarioInvocationError -and
            $scenarioIntegrityError) {
            "Invocation error: $($scenarioInvocationError.Exception.Message) Integrity error: $($scenarioIntegrityError.Exception.Message)"
        }
        elseif ($scenarioInvocationError) {
            $scenarioInvocationError.Exception.Message
        }
        elseif ($scenarioIntegrityError) {
            $scenarioIntegrityError.Exception.Message
        }
        else {
            $null
        }

        $completedScenarios.Add([pscustomobject][ordered]@{
                name = [string]$scenarioEntry.name
                tier = [string]$scenarioEntry.tier
                module = $module
                configuration = $configuration
                status = if ($scenarioPassed) { "passed" } else { "failed" }
                exitStatus = $scenarioExitStatus
                error = $scenarioErrorMessage
            })

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
                status = if ($scenarioPassed) { "passed" } else { "failed" }
                startedAtUtc = $scenarioStartedAt.ToString("o")
                completedAtUtc = $scenarioCompletedAt.ToString("o")
                durationMilliseconds = [Int64][Math]::Round(
                    $scenarioTimer.Elapsed.TotalMilliseconds)
                exitStatus = $scenarioExitStatus
                error = $scenarioErrorMessage
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
                    tlaToolsSha256 = $runTlaToolsHash
                    observedTlcVersion = $metrics.tlcVersion
                    jreVersion = $jreVersion
                    jreSha256 = $runArchiveHash.ToLowerInvariant()
                    javaSha256 = $runJavaHash
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
        if ($scenarioIntegrityError) {
            throw $scenarioIntegrityError
        }
        if ($scenarioExitStatus -ne 0) {
            throw "Scenario '$($scenarioEntry.name)' failed with exit code $scenarioExitStatus."
        }
    }
    Assert-SnapshotIntegrity `
        -SnapshotDirectory $snapshotDirectory `
        -ExpectedInputs $snapshot.expectedInputs
    Assert-HashedFileIntegrity `
        -Inputs $boundArtifactInputs `
        -Description "Bound artifact input"
    Assert-DirectoryIntegrity `
        -Directory $runToolDirectory `
        -ExpectedInventory $runToolInventory `
        -Description "Per-run tool snapshot"
    Assert-SelectedScenarioCompleteness `
        -SelectedScenarios @($scenarios) `
        -CompletedScenarios @($completedScenarios) `
        -Description "Executed scenario selection"
    if ($resultDocument) {
        Assert-SelectedScenarioCompleteness `
            -SelectedScenarios @($scenarios) `
            -CompletedScenarios @($resultScenarios) `
            -Description "Reported scenario selection"
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
        Write-Host "Final result report: $resolvedResultsPath"
    }
    if ($runSucceeded -and -not $KeepStates) {
        Assert-TemporaryChildPath -Path $stateDirectory
        Remove-Item -LiteralPath $stateDirectory -Recurse -Force
    }
    elseif (Test-Path $stateDirectory) {
        Write-Host "TLC state retained at $stateDirectory"
    }
}
