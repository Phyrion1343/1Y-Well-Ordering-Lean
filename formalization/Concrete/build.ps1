param(
  [ValidateRange(1, 32)]
  [int]$Threads = 1,
  [switch]$AuditOnly,
  [ValidateSet('OneYTruth', 'ZeroYConcrete', 'All')]
  [string]$Target = 'All'
)

$ErrorActionPreference = 'Stop'
$taskLake = [System.IO.Path]::GetFullPath(
  (Join-Path $PSScriptRoot '../../.tools/lean-4.33.1-windows/bin/lake.exe'))
if (-not (Test-Path -LiteralPath $taskLake -PathType Leaf)) {
  throw "缺少本工程的 Lean 4.33.1：$taskLake"
}

$taskVersion = & $taskLake --version
if ($LASTEXITCODE -ne 0 -or $taskVersion -notmatch 'Lean version 4\.33\.1\)') {
  throw "工具链版本不符：$taskVersion"
}

$taskPreviousThreads = $env:LEAN_NUM_THREADS
$taskAuditsToRun = @(
  [PSCustomObject]@{
    Target = 'ZeroYConcrete'
    File = 'Audit.lean'
    Count = 14
    Log = 'audit-output.txt'
  },
  [PSCustomObject]@{
    Target = 'OneYTruth'
    File = 'OneYTruthAudit.lean'
    Count = 153
    Log = 'OneYTruth-audit-output.txt'
  }
)
if ($Target -ne 'All') {
  $taskAuditsToRun = @($taskAuditsToRun | Where-Object { $_.Target -eq $Target })
}
$taskBuildTargets = @($taskAuditsToRun | ForEach-Object { $_.Target })
$taskBuildLog = switch ($Target) {
  'ZeroYConcrete' { '.lake/build-source.log' }
  'OneYTruth' { '.lake/OneYTruth-build-source.log' }
  'All' { '.lake/all-build-source.log' }
}
Push-Location -LiteralPath $PSScriptRoot
try {
  $env:LEAN_NUM_THREADS = [string]$Threads
  # Incremental source build. --no-cache disables Lake's external build cache;
  # it does not delete or bypass current local .olean files. Do not run clean.
  # --keep-toolchain retains Lean 4.33.1 for the pinned dependency sources.
  if (-not $AuditOnly) {
    & $taskLake --keep-toolchain --no-cache build @taskBuildTargets 2>&1 |
      Tee-Object -FilePath $taskBuildLog -Append
    if ($LASTEXITCODE -ne 0) {
      throw "Build failed for $($taskBuildTargets -join ', '); see $taskBuildLog."
    }
  }

  # 在成功构建的实际导入环境中检查最终定理的公理依赖。
  foreach ($taskAuditSpec in $taskAuditsToRun) {
    $taskExpected = @(Get-Content -LiteralPath $taskAuditSpec.File | ForEach-Object {
      if ($_ -match '^#print axioms (\S+)\s*$') { $Matches[1] }
    })
    if ($taskExpected.Count -ne $taskAuditSpec.Count -or
        @($taskExpected | Sort-Object -Unique -CaseSensitive).Count -ne $taskExpected.Count) {
      throw "Invalid audit declaration list in $($taskAuditSpec.File): expected $($taskAuditSpec.Count) unique names."
    }

    & $taskLake --keep-toolchain env lean $taskAuditSpec.File 2>&1 |
      Tee-Object -FilePath $taskAuditSpec.Log
    if ($LASTEXITCODE -ne 0) {
      throw "Audit failed for $($taskAuditSpec.Target); see $($taskAuditSpec.Log)."
    }

    $taskAuditText = Get-Content -LiteralPath $taskAuditSpec.Log -Raw
    $taskAudits = [regex]::Matches($taskAuditText,
      "'(?<name>[^']+)' depends on axioms:\s*\[(?<axioms>[^\]]*)\]")
    if ($taskAudits.Count -ne $taskExpected.Count) {
      throw "Audit count mismatch for $($taskAuditSpec.Target): expected $($taskExpected.Count), found $($taskAudits.Count)."
    }
    $taskSeen = [System.Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
    foreach ($taskAudit in $taskAudits) {
      $taskName = $taskAudit.Groups['name'].Value
      if ($taskName -cnotin $taskExpected -or -not $taskSeen.Add($taskName)) {
        throw "Unknown or duplicate audit declaration: $taskName"
      }
      foreach ($taskAxiom in ($taskAudit.Groups['axioms'].Value -split ',')) {
        $taskAxiom = $taskAxiom.Trim()
        if ($taskAxiom -and $taskAxiom -cnotin @('propext', 'Classical.choice', 'Quot.sound')) {
          throw "Audit rejected $taskName : non-whitelisted axiom $taskAxiom"
        }
      }
    }
    Write-Output "$($taskAuditSpec.Target): all $($taskAuditSpec.Count) declarations passed the axiom whitelist audit."
  }
}
finally {
  Pop-Location
  $env:LEAN_NUM_THREADS = $taskPreviousThreads
}
