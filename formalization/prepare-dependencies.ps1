#Requires -Version 5.1
[CmdletBinding()]
param(
    [Alias('VerifyOnly')][switch]$CheckOnly,
    [switch]$Direct,
    [string[]]$Package = @(),
    [string]$DestinationRoot = ''
)

# Restore sources only. Lean installation and compilation are separate steps.
# -CheckOnly never downloads, extracts, patches, or changes a checkout.
$ErrorActionPreference = 'Stop'
$sourceConcrete = Join-Path $PSScriptRoot 'Concrete'
if (-not $DestinationRoot) { $DestinationRoot = Join-Path $PSScriptRoot '..' }
$destination = [IO.Path]::GetFullPath($DestinationRoot).TrimEnd('\', '/')
$concrete = [IO.Path]::GetFullPath((Join-Path $destination 'formalization/Concrete'))
$lock = Get-Content -LiteralPath (Join-Path $sourceConcrete 'dependencies-lock.json') -Raw -Encoding UTF8 |
    ConvertFrom-Json
$utf8 = New-Object Text.UTF8Encoding($false)
$savedGitParameters = $env:GIT_CONFIG_PARAMETERS
if ($Direct) { $env:GIT_CONFIG_PARAMETERS = "'http.proxy=' 'https.proxy='" }

function Get-WithinRoot([string]$Base, [string]$Relative) {
    $result = [IO.Path]::GetFullPath((Join-Path $Base $Relative))
    if (-not $result.StartsWith($destination + [IO.Path]::DirectorySeparatorChar,
            [StringComparison]::OrdinalIgnoreCase)) {
        throw "Dependency path leaves the destination workspace: $Relative"
    }
    return $result
}

function Get-Hash([string]$Path) {
    return (Get-FileHash -LiteralPath $Path -Algorithm SHA256).Hash.ToLowerInvariant()
}

function Get-TextHash([string]$Text) {
    $sha = [Security.Cryptography.SHA256]::Create()
    try {
        return ([BitConverter]::ToString($sha.ComputeHash($utf8.GetBytes($Text)))).Replace('-', '').ToLowerInvariant()
    } finally { $sha.Dispose() }
}

function Invoke-Git([string[]]$GitArguments) {
    & git @GitArguments
    if ($LASTEXITCODE -ne 0) { throw "Git failed: $($GitArguments -join ' ')" }
}

function Assert-PackageFiles($Entry, [string]$Path) {
    $configLean = Join-Path $Path 'lakefile.lean'
    $configToml = Join-Path $Path 'lakefile.toml'
    if (-not ((Test-Path -LiteralPath $configLean -PathType Leaf) -or
            (Test-Path -LiteralPath $configToml -PathType Leaf))) {
        throw "Missing Lake configuration: $Path"
    }
    $toolchain = Join-Path $Path 'lean-toolchain'
    if (-not (Test-Path -LiteralPath $toolchain -PathType Leaf)) { throw "Missing $toolchain" }
    $actual = (Get-Content -LiteralPath $toolchain -Raw -Encoding UTF8).Trim()
    if ($actual -ne $Entry.sourceToolchain) { throw "Unexpected source toolchain in $Path : $actual" }
    if ($Entry.name -eq 'proofwidgets') {
        $js = Join-Path $Path 'widget/js'
        if (-not (Test-Path -LiteralPath (Join-Path $js 'lake.trace') -PathType Leaf)) {
            throw 'ProofWidgets archive must contain its original widget/js/lake.trace.'
        }
        $files = @(Get-ChildItem -LiteralPath $js -Filter '*.js' -File)
        if ($files.Count -ne 23) { throw "Expected 23 locked ProofWidgets JavaScript files; found $($files.Count)." }
    }
}

function Assert-GitCheckout($Entry, [string]$Path) {
    if (-not (Test-Path -LiteralPath (Join-Path $Path '.git'))) {
        throw "A real Git checkout is required at $Path; no Git metadata will be fabricated."
    }
    $actualRoot = (Invoke-Git @('-C', $Path, 'rev-parse', '--show-toplevel')).Trim()
    if ([IO.Path]::GetFullPath($actualRoot).TrimEnd('\', '/') -ne $Path.TrimEnd('\', '/')) {
        throw "Dependency is not its own Git checkout: $Path"
    }
    $head = (Invoke-Git @('-C', $Path, 'rev-parse', 'HEAD')).Trim()
    if ($head -ne $Entry.commit) { throw "Wrong Git HEAD in $Path : expected $($Entry.commit), found $head" }
    $changed = @(Invoke-Git @('-C', $Path, 'diff', '--name-only', 'HEAD', '--'))
    $allowed = @()
    if ($Entry.name -eq 'YesMetaZFC and bms-constructible-bridge') {
        $allowed = @($lock.localProofScriptPatches | ForEach-Object { $_.file })
    }
    foreach ($file in $changed) {
        if ($file -and $file -notin $allowed) { throw "Tracked dependency source was changed: $Path/$file" }
    }
}

function Restore-GitCheckout($Entry, [string]$Path) {
    if (Test-Path -LiteralPath $Path) {
        $pendingFile = Join-Path $Path '.git/zero-y-prepare.json'
        $head = & git -C $Path rev-parse --verify HEAD 2>$null
        if ($LASTEXITCODE -eq 0 -or -not (Test-Path -LiteralPath $pendingFile -PathType Leaf)) {
            Assert-GitCheckout $Entry $Path
            return
        }
        if ($CheckOnly) { throw "Incomplete Git dependency: $Path" }
        $pending = Get-Content -LiteralPath $pendingFile -Raw -Encoding UTF8 | ConvertFrom-Json
        if ($pending.repository -ne $Entry.repository -or $pending.commit -ne $Entry.commit) {
            throw "Unexpected incomplete checkout: $Path"
        }
    } else {
        if ($CheckOnly) { throw "Missing Git dependency: $Path" }
        New-Item -ItemType Directory -Path (Split-Path -Parent $Path) -Force | Out-Null
        # A fixed-commit shallow fetch keeps genuine Git HEAD and avoids a full-history clone.
        Invoke-Git @('init', '-q', $Path)
        Invoke-Git @('-C', $Path, 'config', 'core.autocrlf', 'true')
        Invoke-Git @('-C', $Path, 'remote', 'add', 'origin', $Entry.repository)
        $pendingFile = Join-Path $Path '.git/zero-y-prepare.json'
        [IO.File]::WriteAllText($pendingFile, (@{ repository = $Entry.repository; commit = $Entry.commit } |
            ConvertTo-Json), $utf8)
    }
    Invoke-Git @('-C', $Path, 'fetch', '--depth', '1', 'origin', $Entry.commit)
    Invoke-Git @('-C', $Path, 'checkout', '--detach', $Entry.commit)
    Assert-GitCheckout $Entry $Path
}

function Assert-Archive([string]$Archive, [string]$Expected) {
    if ((Get-Hash $Archive) -ne $Expected) {
        throw "SHA256 mismatch; archive will not be extracted: $Archive"
    }
}

function Get-Archive($Entry, [string]$Archive) {
    if (Test-Path -LiteralPath $Archive -PathType Leaf) {
        Assert-Archive $Archive $Entry.sha256
        return
    }
    if ($CheckOnly) { throw "Missing cached archive for verification: $Archive" }
    New-Item -ItemType Directory -Path (Split-Path -Parent $Archive) -Force | Out-Null
    $partial = $Archive + '.partial'
    if (-not ((Test-Path -LiteralPath $partial -PathType Leaf) -and
            (Get-Hash $partial) -eq $Entry.sha256)) {
        $repoPath = ([Uri]$Entry.repository).AbsolutePath.Trim('/')
        $url = "https://codeload.github.com/$repoPath/tar.gz/$($Entry.commit)"
        $curlArgs = @('-fL', '--retry', '2', '--connect-timeout', '20', '--max-time', '1800',
            '--continue-at', '-', '--output', $partial)
        if ($Direct) { $curlArgs += @('--noproxy', '*') }
        $curlArgs += $url
        & curl.exe @curlArgs
        if ($LASTEXITCODE -ne 0) { throw "Archive download failed; rerun to resume: $partial" }
    }
    Assert-Archive $partial $Entry.sha256
    Move-Item -LiteralPath $partial -Destination $Archive
}

function Restore-Archive($Entry, [string]$Path) {
    $archive = Get-WithinRoot $concrete $Entry.archive
    Get-Archive $Entry $archive
    if (Test-Path -LiteralPath $Path) { return }
    if ($CheckOnly) { throw "Missing extracted dependency: $Path" }
    $repoName = ([Uri]$Entry.repository).Segments[-1].TrimEnd('/')
    $top = "$repoName-$($Entry.commit)"
    $entries = @(& tar.exe -tf $archive)
    if ($LASTEXITCODE -ne 0 -or $entries.Count -eq 0) { throw "Cannot list archive: $archive" }
    foreach ($item in $entries) {
        $normalized = $item.Replace('\', '/')
        if ($normalized -ne "$top/" -and -not $normalized.StartsWith("$top/")) {
            throw "Unexpected archive root: $item"
        }
        if ($normalized -match '(^|/)\.\.(/|$)|:|^/') { throw "Unsafe archive path: $item" }
    }
    $stagingParent = Get-WithinRoot $destination '.tools/dependency-staging'
    $staging = Join-Path $stagingParent ([Guid]::NewGuid().ToString('N'))
    New-Item -ItemType Directory -Path $staging -Force | Out-Null
    try {
        & tar.exe -xf $archive -C $staging
        if ($LASTEXITCODE -ne 0) { throw "Archive extraction failed: $archive" }
        $extracted = Join-Path $staging $top
        Assert-PackageFiles $Entry $extracted
        New-Item -ItemType Directory -Path (Split-Path -Parent $Path) -Force | Out-Null
        # Both source and destination were resolved within this workspace before moving.
        $resolvedSource = (Resolve-Path -LiteralPath $extracted).Path
        if (-not $resolvedSource.StartsWith($stagingParent + [IO.Path]::DirectorySeparatorChar,
                [StringComparison]::OrdinalIgnoreCase)) { throw 'Unexpected extraction location.' }
        Move-Item -LiteralPath $resolvedSource -Destination $Path
    } finally {
        if (Test-Path -LiteralPath $staging) {
            $resolvedStaging = (Resolve-Path -LiteralPath $staging).Path
            if (-not $resolvedStaging.StartsWith($stagingParent + [IO.Path]::DirectorySeparatorChar,
                    [StringComparison]::OrdinalIgnoreCase)) { throw 'Unexpected temporary directory.' }
            Remove-Item -LiteralPath $resolvedStaging -Recurse -Force
        }
    }
}

function Apply-BmsPatches([string]$Path) {
    foreach ($patch in $lock.localProofScriptPatches) {
        $metadata = @(Get-ChildItem -LiteralPath (Join-Path $sourceConcrete 'patches') -Filter '*.json' -File |
            Where-Object {
                $data = Get-Content -LiteralPath $_.FullName -Raw -Encoding UTF8 | ConvertFrom-Json
                $data.file -eq $patch.file -and $data.patchSha256 -eq $patch.patchSha256
            })
        if ($metadata.Count -ne 1) { throw "Cannot locate patch metadata: $($patch.file)" }
        $patchFile = [IO.Path]::ChangeExtension($metadata[0].FullName, '.patch')
        $patchText = [IO.File]::ReadAllText($patchFile).Replace("`r`n", "`n")
        if ((Get-TextHash $patchText) -ne $patch.patchSha256) { throw "Patch SHA256 mismatch: $patchFile" }
        $file = Get-WithinRoot $Path $patch.file
        $text = [IO.File]::ReadAllText($file).Replace("`r`n", "`n")
        # The published source hashes use CRLF. Compare a canonical CRLF view on any checkout.
        $canonicalHash = Get-TextHash ($text.Replace("`n", "`r`n"))
        if ($canonicalHash -eq $patch.patchedSha256) { continue }
        if ($canonicalHash -ne $patch.originalSha256) { throw "BMS source matches neither baseline nor reviewed patch: $file" }
        if ($CheckOnly) { throw "Reviewed BMS patch is not applied: $file" }
        # Preserve the local file until both its baseline hash and patch applicability have passed.
        Invoke-Git @('-C', $Path, 'apply', '--check', '--ignore-space-change', $patchFile)
        Invoke-Git @('-C', $Path, 'apply', '--ignore-space-change', $patchFile)
        $result = [IO.File]::ReadAllText($file).Replace("`r`n", "`n").Replace("`n", "`r`n")
        if ((Get-TextHash $result) -ne $patch.patchedSha256) { throw "Patched source SHA256 mismatch: $file" }
        [IO.File]::WriteAllText($file, $result, $utf8)
    }
}

try {
    foreach ($command in @('git', 'tar.exe', 'curl.exe')) {
        if (-not (Get-Command $command -ErrorAction SilentlyContinue)) { throw "Required command is missing: $command" }
    }
    $selected = @($lock.packages)
    if ($Package.Count -gt 0) {
        foreach ($name in $Package) {
            if ($name -notin @($lock.packages | ForEach-Object { $_.name })) { throw "Unknown package: $name" }
        }
        $selected = @($lock.packages | Where-Object { $_.name -in $Package })
    }
    foreach ($entry in $selected) {
        if ($entry.commit -notmatch '^[0-9a-f]{40}$' -or
                $entry.repository -notmatch '^https://github\.com/[^/]+/[^/]+$') {
            throw "Invalid locked GitHub source: $($entry.name)"
        }
        $path = Get-WithinRoot $concrete $entry.directory
        if ($entry.sourceKind -eq 'git checkout') { Restore-GitCheckout $entry $path }
        elseif ($entry.sourceKind -eq 'official GitHub commit archive') { Restore-Archive $entry $path }
        else { throw "Unsupported locked source kind: $($entry.sourceKind)" }
        Assert-PackageFiles $entry $path
        if ($entry.name -eq 'YesMetaZFC and bms-constructible-bridge') { Apply-BmsPatches $path }
        Write-Host "Verified $($entry.name) @ $($entry.commit)"
    }
    if ($Package.Count -eq 0) {
        foreach ($relative in @('formalization', 'formalization/Concrete')) {
            $project = Get-WithinRoot $destination $relative
            $manifestPath = Join-Path $project 'lake-manifest.json'
            $manifest = Get-Content -LiteralPath $manifestPath -Raw -Encoding UTF8 | ConvertFrom-Json
            foreach ($entry in $manifest.packages) {
                if ($entry.type -ne 'path') { throw "Unexpected non-path dependency in $manifestPath" }
                $config = Get-WithinRoot (Get-WithinRoot $project $entry.dir) $entry.configFile
                if (-not (Test-Path -LiteralPath $config -PathType Leaf)) { throw "Manifest dependency missing: $config" }
            }
        }
        Write-Host 'All 11 locked source dependencies and both Lake path manifests are ready.'
    } else {
        Write-Host "Selected $($selected.Count) dependencies verified; full-project manifest verification was not requested."
    }
    Write-Host 'This checks source identities/configuration and cached archive hashes, not a new Lean build or every extracted source file.'
    Write-Host 'Next: run formalization/build.ps1, then formalization/Concrete/build.ps1. Do not run lake update.'
} finally {
    $env:GIT_CONFIG_PARAMETERS = $savedGitParameters
}
