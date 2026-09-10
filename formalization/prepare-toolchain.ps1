param([switch]$Direct)

# 仅在当前工作区准备官方便携运行时，不修改系统安装或持久 PATH。
$ErrorActionPreference = 'Stop'
$toolsPath = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../.tools'))
$archivePath = Join-Path $toolsPath 'lean-4.33.1-windows.tar.zst'
$url = 'https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-windows.tar.zst'
$expectedSize = 583557483
$expectedHash = 'f63029c0e1e6daed0f4807481b6fcd8f8b77fbce6d63f205c7f9191072387a7a'
New-Item -ItemType Directory -Force -Path $toolsPath | Out-Null

$currentSize = if (Test-Path -LiteralPath $archivePath) {
    (Get-Item -LiteralPath $archivePath).Length
} else { 0 }
if ($currentSize -ne $expectedSize) {
    $curlArgs = @('-fL', '--retry', '2', '--connect-timeout', '20', '-C', '-', '-o', $archivePath)
    if ($Direct) { $curlArgs += @('--noproxy', '*') }
    $curlArgs += $url
    & curl.exe @curlArgs
    if ($LASTEXITCODE -ne 0) { throw 'Download incomplete; rerun to resume.' }
}

$actualHash = (Get-FileHash -LiteralPath $archivePath -Algorithm SHA256).Hash.ToLowerInvariant()
if ($actualHash -ne $expectedHash) { throw 'Official SHA-256 verification failed; archive not extracted.' }
& tar.exe -xf $archivePath -C $toolsPath
if ($LASTEXITCODE -ne 0) { throw 'Runtime extraction failed.' }
& (Join-Path $toolsPath 'lean-4.33.1-windows/bin/lean.exe') --version
if ($LASTEXITCODE -ne 0) { throw 'Runtime check failed.' }
