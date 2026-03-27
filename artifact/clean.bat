@echo off
setlocal EnableExtensions EnableDelayedExpansion

set "SCRIPT_DIR=%~dp0"
if "%SCRIPT_DIR:~-1%"=="\" set "SCRIPT_DIR=%SCRIPT_DIR:~0,-1%"

echo [artifact] Cleaning up previous results from %SCRIPT_DIR%

REM Delete any directories named results-*
for /d %%D in ("%SCRIPT_DIR%\results-*") do (
  rmdir /s /q "%%~fD" >nul 2>&1
)

REM Delete any files named results-*
for %%F in ("%SCRIPT_DIR%\results-*") do (
  del /f /q "%%~fF" >nul 2>&1
)

endlocal
