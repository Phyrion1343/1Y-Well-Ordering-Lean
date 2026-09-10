param(
    [string]$LeanBin = '',
    [switch]$WarningsAsErrors
)

$ErrorActionPreference = 'Stop'
$upstreamPath = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../research/BMS-Well-Ordering-Lean'))
$expectedCommit = 'bae7e3d741f24a56d80da9b99c1345562cd10c2d'
$actualCommit = (& git -C $upstreamPath rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $actualCommit -ne $expectedCommit) {
    throw "BMS dependency must be at commit $expectedCommit; found $actualCommit"
}

if (!$LeanBin) {
    $portableBin = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../.tools/lean-4.33.1-windows/bin'))
    if (Test-Path -LiteralPath (Join-Path $portableBin 'lake.exe')) {
        $LeanBin = $portableBin
    } else {
        $lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
        if (!$lakeCommand) {
            throw 'Lean toolchain unavailable. Run prepare-toolchain.ps1 or provide -LeanBin.'
        }
        $LeanBin = Split-Path -Parent $lakeCommand.Source
    }
}

$savedPath = $env:PATH
Push-Location $PSScriptRoot
try {
    $env:PATH = "$LeanBin;$savedPath"
    $leanVersion = & (Join-Path $LeanBin 'lean.exe') --version
    if ($LASTEXITCODE -ne 0) { throw 'Lean version check failed.' }
    if ($leanVersion -notmatch 'version 4\.33\.1[,)]') {
        throw "Lean 4.33.1 required; found $leanVersion"
    }
    Write-Host $leanVersion
    # Incremental build: existing local artifacts are reused. Style warnings
    # remain visible; ordinary Lean errors always cause a nonzero exit.
    $buildArguments = @('build')
    if ($WarningsAsErrors) { $buildArguments = @('--wfail') + $buildArguments }
    & (Join-Path $LeanBin 'lake.exe') @buildArguments
    if ($LASTEXITCODE -ne 0) { throw 'Lean build failed.' }
} finally {
    $env:PATH = $savedPath
    Pop-Location
}
