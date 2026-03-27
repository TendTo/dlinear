@echo off
setlocal EnableExtensions EnableDelayedExpansion

REM Args: run name (default: empty)
set "RUN_NAME=%~1"

set "SCRIPT_DIR=%~dp0"
if "%SCRIPT_DIR:~-1%"=="\" set "SCRIPT_DIR=%SCRIPT_DIR:~0,-1%"

set "IMAGE_TAG=qest-formats-ae:2026"
set "IMAGE_TAR=%SCRIPT_DIR%\qest-formats-ae-image.tar.gz"

if "%RUN_NAME%"=="" (
  set "RESULTS_DIR=%SCRIPT_DIR%\results"
) else (
  set "RESULTS_DIR=%SCRIPT_DIR%\results-%RUN_NAME%"
)
set "INSTANCES_DIR=%SCRIPT_DIR%\instances"

REM Load docker image from tar if needed.
docker image inspect "%IMAGE_TAG%" >nul 2>&1
if errorlevel 1 (
  if exist "%IMAGE_TAR%" (
    echo [artifact] Loading docker image from %IMAGE_TAR%
    docker load -i "%IMAGE_TAR%" >nul
  )
)

echo [artifact] Launching the Jupyter notebook to visualize the results
REM Use --mount instead of -v to avoid Windows drive-letter ':' parsing issues.
docker run -p 8888:8888 --rm ^
  --mount "type=bind,source=%RESULTS_DIR%,target=/work/results" ^
  --mount "type=bind,source=%INSTANCES_DIR%,target=/work/instances" ^
  "%IMAGE_TAG%"

endlocal
