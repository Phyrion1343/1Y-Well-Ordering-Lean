#Requires -Version 5.1
[CmdletBinding()]
param(
    [Alias('VerifyOnly')][switch]$CheckOnly,
    [switch]$Direct,
    [string[]]$Package = @(),
    [string]$DestinationRoot = ''
)

# All dependency sources are vendored. This command only reads local files:
# no Git checkout, archive, patch application, download, or build is required.
# CheckOnly/VerifyOnly are retained as aliases for this default verification.
$ErrorActionPreference = 'Stop'
if ($Direct) { Write-Warning '-Direct is deprecated and ignored; dependency verification never uses the network.' }
if (!$DestinationRoot) { $DestinationRoot = Join-Path $PSScriptRoot '..' }
$destination = $ExecutionContext.SessionState.Path.GetUnresolvedProviderPathFromPSPath($DestinationRoot)
$destinationPrefix = $destination.TrimEnd([char[]]'\/') + [IO.Path]::DirectorySeparatorChar
$pathComparison = if ($env:OS -eq 'Windows_NT') { [StringComparison]::OrdinalIgnoreCase } else { [StringComparison]::Ordinal }
$pathComparer = if ($env:OS -eq 'Windows_NT') { [StringComparer]::OrdinalIgnoreCase } else { [StringComparer]::Ordinal }
$checkedDirectories = [Collections.Generic.HashSet[string]]::new($pathComparer)

function Assert-NoLink([string]$Path) {
    # Reject symlinks/junctions inside the repository so lexical containment
    # cannot redirect a manifest entry outside the intended source tree.
    $cursor = $Path
    while ($cursor.StartsWith($destinationPrefix, $pathComparison)) {
        if ($checkedDirectories.Contains($cursor)) { break }
        $item = Get-Item -LiteralPath $cursor -Force -ErrorAction Stop
        if (($item.Attributes -band [IO.FileAttributes]::ReparsePoint) -ne 0) {
            throw "Dependency paths must not traverse symlinks or junctions: $cursor"
        }
        if ($item.PSIsContainer) { [void]$checkedDirectories.Add($cursor) }
        $cursor = Split-Path -Parent $cursor
    }
}

function Get-WithinRoot([string]$Base, [string]$Relative) {
    if ([string]::IsNullOrWhiteSpace($Relative) -or [IO.Path]::IsPathRooted($Relative)) {
        throw "Expected a nonempty repository-relative dependency path: $Relative"
    }
    $result = [IO.Path]::GetFullPath((Join-Path $Base $Relative.Replace('\', '/')))
    if (!$result.StartsWith($destinationPrefix, $pathComparison)) {
        throw "Dependency path leaves the destination repository: $Relative"
    }
    Assert-NoLink $result
    return $result
}

function Read-Json([string]$Path) {
    if (!(Test-Path -LiteralPath $Path -PathType Leaf)) { throw "Missing required manifest: $Path" }
    return Get-Content -LiteralPath $Path -Raw -Encoding UTF8 | ConvertFrom-Json
}

$concrete = Get-WithinRoot $destination 'formalization/Concrete'
$vendor = Get-WithinRoot $destination 'vendor'
$vendorPrefix = $vendor.TrimEnd([char[]]'\/') + [IO.Path]::DirectorySeparatorChar
$lock = Read-Json (Get-WithinRoot $concrete 'dependencies-lock.json')
$sourceManifest = Read-Json (Get-WithinRoot $vendor 'source-manifest.json')
if ($sourceManifest.format -ne 1 -or !$sourceManifest.files -or @($sourceManifest.files).Count -eq 0) {
    throw 'vendor/source-manifest.json must have format 1 and a nonempty files array.'
}
if (!$lock.packages -or @($lock.packages).Count -eq 0) { throw 'Dependency lock has no packages.' }

# A dictionary also rejects duplicate/case-colliding paths on every platform,
# so the checked source set can be used on Windows as well as Linux.
$sources = [Collections.Generic.Dictionary[string,object]]::new([StringComparer]::OrdinalIgnoreCase)
foreach ($entry in $sourceManifest.files) {
    $relative = [string]$entry.path
    $parts = $relative -split '/'
    if ([string]::IsNullOrWhiteSpace($relative) -or $relative.Contains('\') -or
            $relative.Contains(':') -or [IO.Path]::IsPathRooted($relative) -or
            @($parts | Where-Object { $_ -in @('', '.', '..', '.lake', '.git') }).Count -gt 0 -or
            $relative -eq 'source-manifest.json' -or $entry.sha256 -notmatch '^[0-9a-fA-F]{64}$') {
        throw "Invalid vendor source-manifest entry: $relative"
    }
    if ($sources.ContainsKey($relative)) { throw "Duplicate vendor source path: $relative" }
    $sources.Add($relative, $entry)
}

$packagePaths = [Collections.Generic.Dictionary[string,string]]::new([StringComparer]::OrdinalIgnoreCase)
foreach ($entry in $lock.packages) {
    $name = [string]$entry.name
    if ([string]::IsNullOrWhiteSpace($name) -or $packagePaths.ContainsKey($name)) {
        throw "Empty or duplicate dependency package name: $name"
    }
    # directory retains the lock's historical base: formalization/Concrete.
    $path = Get-WithinRoot $concrete ([string]$entry.directory)
    if (!$path.StartsWith($vendorPrefix, $pathComparison) -or
            !(Test-Path -LiteralPath $path -PathType Container)) {
        throw "Locked package must be a directory below vendor: $name ($path)"
    }
    $packagePaths.Add($name, $path)
}
foreach ($name in $Package) {
    if (!$packagePaths.ContainsKey($name)) { throw "Unknown package: $name" }
}
$selected = @($lock.packages | Where-Object { $Package.Count -eq 0 -or $_.name -in $Package })
$selectedPrefixes = @($selected | ForEach-Object {
    $packagePaths[$_.name].Substring($vendorPrefix.Length).Replace('\', '/') + '/'
})

$verified = 0
foreach ($entry in $sourceManifest.files) {
    $relative = [string]$entry.path
    $wanted = $Package.Count -eq 0
    if (!$wanted) {
        foreach ($prefix in $selectedPrefixes) {
            if ($relative.StartsWith($prefix, [StringComparison]::OrdinalIgnoreCase)) { $wanted = $true; break }
        }
    }
    if (!$wanted) { continue }
    $path = Get-WithinRoot $vendor $relative
    if (!(Test-Path -LiteralPath $path -PathType Leaf)) { throw "Missing vendored source file: $relative" }
    $hash = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash
    if ($hash -ine $entry.sha256) { throw "SHA256 mismatch for vendor/$relative" }
    $verified++
    if ($verified % 1000 -eq 0) { Write-Host "Verified $verified vendored files..." }
}

# Account for every source file, not just entries that happen to be listed.
# Exempt only .lake directories, this manifest, and ProofWidgets' exact
# generated package-lock hash cache. Source .hash/.trace files stay checked.
$walk = [Collections.Generic.Stack[string]]::new()
if ($Package.Count -eq 0) { $walk.Push($vendor) }
else { foreach ($entry in $selected) { $walk.Push($packagePaths[$entry.name]) } }
while ($walk.Count -gt 0) {
    foreach ($item in Get-ChildItem -LiteralPath $walk.Pop() -Force) {
        if ($item.PSIsContainer -and $item.Name -eq '.lake') { continue }
        Assert-NoLink $item.FullName
        if ($item.PSIsContainer) { $walk.Push($item.FullName); continue }
        $relative = $item.FullName.Substring($vendorPrefix.Length).Replace('\', '/')
        if ($relative -eq 'source-manifest.json') { continue }
        # Assert-NoLink above also applies to this generated cache file.
        if ($relative -ceq 'proofwidgets/widget/package-lock.json.hash') { continue }
        if (!$sources.ContainsKey($relative)) { throw "Unlisted vendored source file: $relative" }
    }
}

foreach ($entry in $selected) {
    $path = $packagePaths[$entry.name]
    $prefix = $path.Substring($vendorPrefix.Length).Replace('\', '/') + '/'
    if (@($sourceManifest.files | Where-Object {
            $_.path.StartsWith($prefix, [StringComparison]::OrdinalIgnoreCase)
        }).Count -eq 0) { throw "No source hashes for locked package: $($entry.name)" }
    if (!(Test-Path -LiteralPath (Join-Path $path 'lakefile.lean') -PathType Leaf) -and
            !(Test-Path -LiteralPath (Join-Path $path 'lakefile.toml') -PathType Leaf)) {
        throw "Missing Lake configuration for package: $($entry.name)"
    }
    $toolchain = Get-WithinRoot $path 'lean-toolchain'
    $actual = (Get-Content -LiteralPath $toolchain -Raw -Encoding UTF8).Trim()
    if ($entry.sourceToolchain -and $actual -cne $entry.sourceToolchain) {
        throw "Unexpected source toolchain in $path : $actual"
    }
    Write-Host "Verified package: $($entry.name)"
}

# Always inspect both project manifests, including a package-filtered run.
# A path dependency may be vendor code or another project inside this repo.
foreach ($relative in @('formalization', 'formalization/Concrete')) {
    $project = Get-WithinRoot $destination $relative
    $manifestPath = Get-WithinRoot $project 'lake-manifest.json'
    $manifest = Read-Json $manifestPath
    if (!$manifest.packages -or @($manifest.packages).Count -eq 0) {
        throw "Empty Lake dependency manifest: $manifestPath"
    }
    foreach ($entry in $manifest.packages) {
        if ($entry.type -cne 'path') { throw "Non-path dependency in $manifestPath : $($entry.name)" }
        $dependency = Get-WithinRoot $project ([string]$entry.dir)
        $config = Get-WithinRoot $dependency ([string]$entry.configFile)
        if (!(Test-Path -LiteralPath $config -PathType Leaf)) { throw "Manifest dependency configuration missing: $config" }
    }
    Write-Host "Verified local path manifest: $relative/lake-manifest.json"
}
Write-Host "Verified $verified SHA256 source hashes across $($selected.Count) selected packages; both Lake path manifests are local."
if ($Package.Count -gt 0) { Write-Host 'Package selection verifies only those source subtrees; omit -Package before a full build.' }
Write-Host 'Verification is read-only and offline. No Git metadata or cached source archives are needed.'
