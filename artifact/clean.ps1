#!/usr/bin/env pwsh
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path

Write-Host "[artifact] Cleaning up previous results from $ScriptDir"

# Match the bash behavior: rm -rf ${SCRIPT_DIR}/results-*
Get-ChildItem -LiteralPath $ScriptDir -Filter 'results-*' -Force -ErrorAction SilentlyContinue |
  ForEach-Object {
    try {
      Remove-Item -LiteralPath $_.FullName -Recurse -Force -ErrorAction Stop
    } catch {
      # Re-throw with a clearer message
      throw "Failed to remove '$($_.FullName)': $($_.Exception.Message)"
    }
  }
