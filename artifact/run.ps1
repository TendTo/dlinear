#!/usr/bin/env pwsh
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

# Args: run name (default: smoke), local limit (default: 6)
$RunName = if ($args.Count -ge 1 -and $args[0]) { [string]$args[0] } else { 'smoke' }
$LocalLimit = if ($args.Count -ge 2 -and $args[1]) { [int]$args[1] } else { 6 }

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$ImageTag = 'qest-formats-ae:2026'
$ImageTar = Join-Path $ScriptDir 'qest-formats-ae-image.tar.gz'
$ResultsDir = Join-Path $ScriptDir ("results-$RunName")
$InstancesDir = Join-Path $ScriptDir 'instances'

New-Item -ItemType Directory -Force -Path $ResultsDir | Out-Null
New-Item -ItemType Directory -Force -Path $InstancesDir | Out-Null

$ResultsDirAbs = (Resolve-Path -Path $ResultsDir).Path
$InstancesDirAbs = (Resolve-Path -Path $InstancesDir).Path

# Run as the host user on Linux/macOS so bind-mounted results are writable.
$userArgs = @()
$onWindows = [System.Runtime.InteropServices.RuntimeInformation]::IsOSPlatform(
  [System.Runtime.InteropServices.OSPlatform]::Windows
)
if (-not $onWindows) {
  try {
    $uid = (& id -u).Trim()
    $gid = (& id -g).Trim()
    if ($uid -and $gid) {
      $userArgs = @('--user', "$uid`:$gid")
    }
  } catch {
    # If id is unavailable, just omit --user.
  }
}

# Load docker image from tar if needed.
& docker image inspect $ImageTag *> $null
$imageExists = ($LASTEXITCODE -eq 0)
if (-not $imageExists -and (Test-Path -LiteralPath $ImageTar)) {
  Write-Host "[artifact] Loading docker image from $ImageTar"
  & docker load -i $ImageTar *> $null
}

Write-Host "[artifact] Running $RunName test"
& docker run --rm @userArgs `
  --mount "type=bind,source=$ResultsDirAbs,target=/results" `
  --mount "type=bind,source=$InstancesDirAbs,target=/instances" `
  --entrypoint ./run_impl.sh `
  $ImageTag $RunName $LocalLimit

Write-Host "[artifact] Launching the Jupyter notebook to visualize the results"
& docker run -p 8888:8888 --rm `
  --mount "type=bind,source=$ResultsDirAbs,target=/work/results" `
  --mount "type=bind,source=$InstancesDirAbs,target=/work/instances" `
  $ImageTag
