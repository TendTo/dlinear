@echo off
setlocal EnableExtensions EnableDelayedExpansion

REM Args: run name (default: smoke), local limit (default: 6)
set "RUN_NAME=%~1"
if "%RUN_NAME%"=="" set "RUN_NAME=smoke"

set "LOCAL_LIMIT=%~2"
if "%LOCAL_LIMIT%"=="" set "LOCAL_LIMIT=6"

set "SCRIPT_DIR=%~dp0"
if "%SCRIPT_DIR:~-1%"=="\" set "SCRIPT_DIR=%SCRIPT_DIR:~0,-1%"

set "IMAGE_TAG=qest-formats-ae:2026"
set "IMAGE_TAR=%SCRIPT_DIR%\qest-formats-ae-image.tar.gz"
set "RESULTS_DIR=%SCRIPT_DIR%\results-%RUN_NAME%"
set "INSTANCES_DIR=%SCRIPT_DIR%\instances"

if not exist "%RESULTS_DIR%" mkdir "%RESULTS_DIR%" >nul
if not exist "%INSTANCES_DIR%" mkdir "%INSTANCES_DIR%" >nul

REM Load docker image from tar if needed.
docker image inspect "%IMAGE_TAG%" >nul 2>&1
if errorlevel 1 (
  if exist "%IMAGE_TAR%" (
    echo [artifact] Loading docker image from %IMAGE_TAR%
    docker load -i "%IMAGE_TAR%" >nul
  )
)

echo [artifact] Running %RUN_NAME% test
REM Use --mount instead of -v to avoid Windows drive-letter ':' parsing issues.
docker run --rm ^
  --mount "type=bind,source=%RESULTS_DIR%,target=/results" ^
  --mount "type=bind,source=%INSTANCES_DIR%,target=/instances" ^
  --entrypoint ./run_impl.sh ^
  "%IMAGE_TAG%" "%RUN_NAME%" "%LOCAL_LIMIT%"

echo [artifact] Launching the Jupyter notebook to visualize the results
docker run -p 8888:8888 --rm ^
  --mount "type=bind,source=%RESULTS_DIR%,target=/work/results" ^
  --mount "type=bind,source=%INSTANCES_DIR%,target=/work/instances" ^
  "%IMAGE_TAG%"

endlocal
