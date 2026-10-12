param(
  [Parameter(Mandatory=$true)][string]$LeanExecutable,
  [Parameter(Mandatory=$true)][string]$PackageRoot,
  [string[]]$Modules = @('Basic', 'Arithmetic', 'Density', 'Equality', 'PathAverage',
    'PeriodicDensity', 'Lower', 'LowerCount', 'Zero', 'Upper', 'Main', 'W01')
)
$ErrorActionPreference = 'Stop'
$leanExe = (Resolve-Path -LiteralPath $LeanExecutable).Path
$packagePath = (Resolve-Path -LiteralPath $PackageRoot).Path
$outputRoot = Join-Path $PSScriptRoot '.lake/build/lib/lean'
New-Item -ItemType Directory -Force -Path (Join-Path $outputRoot 'W01') | Out-Null
$libraryPaths = @($outputRoot)
foreach ($package in Get-ChildItem -LiteralPath $packagePath -Directory) {
  $library = Join-Path $package.FullName '.lake/build/lib/lean'
  if (Test-Path -LiteralPath $library) { $libraryPaths += $library }
}
$previousLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = $libraryPaths -join [System.IO.Path]::PathSeparator
Push-Location $PSScriptRoot
try {
  & $leanExe --version
  foreach ($module in $Modules) {
    $source = if ($module -eq 'W01') { 'W01.lean' } else { "W01/$module.lean" }
    $target = if ($module -eq 'W01') { 'W01.olean' } else { "W01/$module.olean" }
    Write-Output "BUILD $source"
    & $leanExe -j 2 -s 131072 -o (Join-Path $outputRoot $target) $source
    if ($LASTEXITCODE -ne 0) { throw "Lean compilation failed: $source" }
  }
  Write-Output 'BUILD_SUCCEEDED'
} finally {
  Pop-Location
  $env:LEAN_PATH = $previousLeanPath
}
