@echo off
setlocal EnableExtensions EnableDelayedExpansion

set "SCRIPT_DIR=%~dp0"
if "%SCRIPT_DIR:~-1%"=="\" set "SCRIPT_DIR=%SCRIPT_DIR:~0,-1%"
set "IMAGE_TAG=qest-formats-ae:2026"
set "IMAGE_TAR=%SCRIPT_DIR%\qest-formats-ae-image.tar.gz"

REM Load docker image from tar if needed.
docker image inspect "%IMAGE_TAG%" >nul 2>&1
if errorlevel 1 (
  if exist "%IMAGE_TAR%" (
    echo [artifact] Loading docker image from %IMAGE_TAR%
    docker load -i "%IMAGE_TAR%" >nul
  )
)

echo [artifact] Running dlinear
docker run --rm --entrypoint ./binary_impl.sh "%IMAGE_TAG%" %* 
