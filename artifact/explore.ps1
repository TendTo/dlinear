#!/usr/bin/env pwsh
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

# Args: run name (default: empty)
$RunName = if ($args.Count -ge 1 -and $args[0]) { [string]$args[0] } else { '' }

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ImageTag = 'qest-formats-ae:2026'
$ImageTar = Join-Path $ScriptDir 'qest-formats-ae-image.tar.gz'

$ResultsDir = if ([string]::IsNullOrEmpty($RunName)) {
  Join-Path $ScriptDir 'results'
} else {
  Join-Path $ScriptDir ("results-$RunName")
}
$InstancesDir = Join-Path $ScriptDir 'instances'

$ResultsDirAbs = (Resolve-Path -Path $ResultsDir).Path
$InstancesDirAbs = (Resolve-Path -Path $InstancesDir).Path

# Load docker image from tar if needed.
& docker image inspect $ImageTag *> $null
$imageExists = ($LASTEXITCODE -eq 0)
if (-not $imageExists -and (Test-Path -LiteralPath $ImageTar)) {
  Write-Host "[artifact] Loading docker image from $ImageTar"
  & docker load -i $ImageTar *> $null
}

Write-Host "[artifact] Launching the Jupyter notebook to visualize the results"
& docker run -p 8888:8888 --rm `
  --mount "type=bind,source=$ResultsDirAbs,target=/work/results" `
  --mount "type=bind,source=$InstancesDirAbs,target=/work/instances" `
  $ImageTag
