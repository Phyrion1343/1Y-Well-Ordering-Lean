#Requires -Version 5.1
param(
    [string]$LeanBin = '',
    [switch]$WarningsAsErrors
)

$ErrorActionPreference = 'Stop'
& (Join-Path $PSScriptRoot 'prepare-dependencies.ps1') -CheckOnly

function Find-Tool([string]$Directory, [string]$Name) {
    $names = if ($env:OS -eq 'Windows_NT') { @("$Name.exe", $Name) } else { @($Name, "$Name.exe") }
    foreach ($candidate in $names) {
        $path = Join-Path $Directory $candidate
        if (Test-Path -LiteralPath $path -PathType Leaf) { return $path }
    }
    throw "Missing $Name in toolchain directory: $Directory"
}

if (!$LeanBin) {
    foreach ($portable in @('lean-4.33.1-windows', 'lean-4.33.1-linux', 'lean-4.33.1')) {
        $portableBin = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot "../.tools/$portable/bin"))
        $lakeName = if ($env:OS -eq 'Windows_NT') { 'lake.exe' } else { 'lake' }
        if (Test-Path -LiteralPath (Join-Path $portableBin $lakeName) -PathType Leaf) {
            $LeanBin = $portableBin
            break
        }
    }
    if (!$LeanBin) {
        $lakeCommand = Get-Command lake -CommandType Application -ErrorAction SilentlyContinue |
            Select-Object -First 1
        if (!$lakeCommand) {
            throw 'Lean toolchain unavailable. Run prepare-toolchain.ps1 or provide -LeanBin.'
        }
        $LeanBin = Split-Path -Parent $lakeCommand.Source
    }
}
$LeanBin = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($LeanBin)
$taskLean = Find-Tool $LeanBin 'lean'
$taskLake = Find-Tool $LeanBin 'lake'

$savedPath = $env:PATH
Push-Location -LiteralPath $PSScriptRoot
try {
    $env:PATH = $LeanBin + [IO.Path]::PathSeparator + $savedPath
    $leanVersion = (& $taskLean --version) -join [Environment]::NewLine
    if ($LASTEXITCODE -ne 0) { throw 'Lean version check failed.' }
    if ($leanVersion -notmatch 'version 4\.33\.1(?:[,)]|\s|$)') {
        throw "Lean 4.33.1 required; found $leanVersion"
    }
    $lakeVersion = (& $taskLake --version) -join [Environment]::NewLine
    if ($LASTEXITCODE -ne 0 -or $lakeVersion -notmatch 'Lean version 4\.33\.1(?:[,)]|\s|$)') {
        throw "Lake must use Lean 4.33.1; found $lakeVersion"
    }
    Write-Host $leanVersion
    New-Item -ItemType Directory -Path '.lake' -Force | Out-Null
    # Incremental build: existing local artifacts are reused. Style warnings
    # remain visible; ordinary Lean errors always cause a nonzero exit.
    # Do not download Lake's external build cache or change the pinned toolchain.
    $buildArguments = @('--keep-toolchain', '--no-cache', 'build')
    if ($WarningsAsErrors) { $buildArguments = @('--wfail') + $buildArguments }
    & $taskLake @buildArguments 2>&1 | Tee-Object -FilePath '.lake/core-build-source.log' -Append
    if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }
} finally {
    $env:PATH = $savedPath
    Pop-Location
}
