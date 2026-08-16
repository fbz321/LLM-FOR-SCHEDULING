param(
  [Parameter(Mandatory = $true)][string]$File,
  [switch]$UseLocalToolchain
)

# Single-file compile helper: `lake env lean <File>` against the already-built
# project .olean files. Does NOT trigger a full `lake build`.
$repoRoot = $PSScriptRoot

if ($UseLocalToolchain) {
  $leanRoot = Join-Path (Split-Path -Parent $repoRoot) "lean-4.33.0-rc1-windows"
  if (-not (Test-Path $leanRoot)) {
    throw "Local toolchain not found: $leanRoot"
  }
  $env:PATH = "$leanRoot\bin;$env:PATH"
  $env:LAKE_OVERRIDE_LEAN = "true"
}

$env:ELAN_NO_OVERRIDE_NOTICE = "1"

Push-Location $repoRoot
try {
  & lake env lean $File 2>&1
  exit $LASTEXITCODE
} finally {
  Pop-Location
}
