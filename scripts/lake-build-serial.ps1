param(
  [string]$RootFile = "Mathlib.lean",
  [int]$Start = 0,
  [int]$Count = 0,
  [int]$Retries = 2,
  [int]$LeanThreads = 1,
  [switch]$UseLocalToolchain
)

$ErrorActionPreference = "Stop"

function Get-ImportTargets {
  param([string]$Path)

  Get-Content $Path | ForEach-Object {
    if ($_ -match '^(public\s+)?import\s+([A-Za-z0-9_.]+)\s*$') {
      $module = $matches[2]
      if ($module -ne "Std" -and $module -ne "Batteries") {
        $module.Replace('.', '\') + ".lean"
      }
    }
  }
}

if ($UseLocalToolchain) {
  $repoRoot = Split-Path -Parent $PSScriptRoot
  $leanRoot = Join-Path (Split-Path -Parent $repoRoot) "lean-4.33.0-rc1-windows"
  if (-not (Test-Path $leanRoot)) {
    throw "Local toolchain not found: $leanRoot"
  }
  $env:PATH = "$leanRoot\bin;$env:PATH"
  $env:LAKE_OVERRIDE_LEAN = "true"
}

$env:LEAN_NUM_THREADS = $LeanThreads.ToString()

$targets = @(Get-ImportTargets -Path $RootFile)
if ($Start -gt 0) {
  if ($Start -ge $targets.Count) {
    throw "Start index $Start is out of range for $($targets.Count) targets."
  }
  $targets = $targets[$Start..($targets.Count - 1)]
}
if ($Count -gt 0 -and $Count -lt $targets.Count) {
  $targets = $targets[0..($Count - 1)]
}

Write-Host "Serial build target count: $($targets.Count); LEAN_NUM_THREADS=$env:LEAN_NUM_THREADS"

$index = 0
foreach ($target in $targets) {
  $index++
  $attempt = 0
  while ($true) {
    $attempt++
    Write-Host "[$index/$($targets.Count)] attempt $attempt building $target"
    & lake build $target
    if ($LASTEXITCODE -eq 0) {
      break
    }
    if ($attempt -gt $Retries) {
      throw "Failed to build $target after $attempt attempts."
    }
    Start-Sleep -Seconds 1
  }
}

Write-Host "Serial build finished."
