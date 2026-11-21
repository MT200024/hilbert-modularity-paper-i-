# Run in Windows PowerShell from the project's root directory.
$ErrorActionPreference = 'Stop'
if (-not (Test-Path '.\lakefile.toml')) {
    throw 'Open a terminal in the directory containing lakefile.toml.'
}
if (-not (Get-Command lake -ErrorAction SilentlyContinue)) {
    throw 'Lake not found. Install Lean 4/Elan using the VS Code Lean extension.'
}
New-Item -ItemType Directory -Path '.\build-logs' -Force | Out-Null
Write-Host 'Checking the pinned toolchain and Mathlib cache...'
& lake exe cache get
if ($LASTEXITCODE -ne 0) { throw 'Mathlib cache/dependency fetch failed.' }
Write-Host 'Building the full HilbertModularity library...'
& lake build 2>&1 | Tee-Object -FilePath '.\build-logs\lake-build.log'
if ($LASTEXITCODE -ne 0) { throw 'lake build failed: inspect build-logs\lake-build.log' }
Write-Host 'Checking the revised alignment module...'
& lake env lean '.\HilbertModularity\Hypergeometric\RevisedPaperI.lean' 2>&1 |
    Tee-Object -FilePath '.\build-logs\revised-module.log'
if ($LASTEXITCODE -ne 0) { throw 'Revised module check failed.' }
Write-Host 'Build and revised module check returned exit code 0.'
Write-Host 'The exact Euler/RM twist identification remains unproved: read MANUSCRIPT_ALIGNMENT.md.'
