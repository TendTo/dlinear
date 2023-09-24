#!/bin/bash
# Script template author: Michel VONGVILAY (https://www.uxora.com)
# License: CC-BY-SA Creative Commons License
#================================================================
# HEADER
#================================================================
#% SYNOPSIS
#+    ${SCRIPT_NAME} [-c/--cleanup] [-s/--stub] [-d/--dry-run] [-t/--test] [-b/--build]
#%
#% DESCRIPTION
#%    Upload pydlinear python package to pypi.
#%    Requires an account on pypi.org
#%
#% OPTIONS
#%    -h, --help                  Print this help tooltip
#%    -v, --version               Print script information
#%    -c, --cleanup               Cleanup build and dist folders. Does not continue with the build
#%    -s, --stub                  Generate stubs for pydlinear
#%    -d, --dry-run               Stop before building with python and uploading to pypi
#%    -b, --build                 Force a build with bazel. Normally, the build step is included in the pip install command
#%    -t, --test                  Upload to testpypi instead of pypi
#%
#% EXAMPLES
#%    ${SCRIPT_NAME}
#%    ${SCRIPT_NAME} --test # Upload to testpypi
#%    ${SCRIPT_NAME} --dry-run # Just checks if the prerequesites are met
#%    ${SCRIPT_NAME} --build --stub -dry-run # Build, generate stubs and stop before uploading
#%    ${SCRIPT_NAME} --cleanup # Removes build and dist folders
#%
#================================================================
#- IMPLEMENTATION
#-    version         ${SCRIPT_NAME} 0.0.1
#-    author          TendTo
#-    copyright       Copyright (c) https://github.com/TendTo
#-    license         GNU General Public License
#-
#================================================================
# END_OF_HEADER
#================================================================

# DESC: Usage help and version info
# ARGS: None
# OUTS: None
# NOTE: Used to document the usage of the script
#       and to display its version when requested or
#       if some arguments are not valid
usage() { printf "Usage: "; head -${script_headsize:-99} ${0} | grep -e "^#+" | sed -e "s/^#+[ ]*//g" -e "s/\${SCRIPT_NAME}/${script_name}/g" ; }
usagefull() { head -${script_headsize:-99} ${0} | grep -e "^#[%+-]" | sed -e "s/^#[%+-]//g" -e "s/\${SCRIPT_NAME}/${script_name}/g" ; }
scriptinfo() { head -${script_headsize:-99} ${0} | grep -e "^#-" | sed -e "s/^#-//g" -e "s/\${SCRIPT_NAME}/${script_name}/g"; }

# DESC: Generic script initialisation
# ARGS: $@ (optional): Arguments provided to the script
# OUTS: $orig_cwd: The current working directory when the script was run
#       $script_path: The full path to the script
#       $script_dir: The directory path of the script
#       $script_name: The file name of the script
#       $script_params: The original parameters provided to the script
#       $ta_none: The ANSI control code to reset all text attributes
# NOTE: $script_path only contains the path that was used to call the script
#       and will not resolve any symlinks which may be present in the path.
#       You can use a tool like realpath to obtain the "true" path. The same
#       caveat applies to both the $script_dir and $script_name variables.
function script_init() {
    # Useful variables
    readonly orig_cwd="$PWD"
    readonly script_params="$*"
    readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 || exit ; pwd -P )"
    readonly script_dir="$(dirname "${BASH_SOURCE[0]}")"
    readonly script_name="$(basename "${BASH_SOURCE[0]}")"
    readonly script_headsize=$(head -200 "${0}" |grep -n "^# END_OF_HEADER" | cut -f1 -d:)
}

# DESC: Verify the user wants to continue asking (y/n)
# ARGS: $1: Message to display
function confirm() {
    local message="$1"
    if [[ -z "${yes}" ]]; then
        read -p "${message}Continue? [y/N] " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            >&2 echo "Operation aborted by user"
            exit 1
        fi
    fi
}

# DESC: Parameter parser
# ARGS: $@ (optional): Arguments provided to the script
# OUTS: Variables indicating command-line parameters and options
function parse_args
{
    # Local variable
    local param
    # Positional args
    args=()

    test_upload=""
    dry_run=false
    cleanup=false
    stub=false
    build=false

    # Named args
    while [ $# -gt 0 ]; do
        param="$1"
        shift
        case "$param" in
            -h )
                usage
                exit 0
            ;;
            --help )
                usagefull
                exit 0
            ;;
            -v | --version )
                scriptinfo
                exit 0
            ;;
            -c | --cleanup )
                cleanup=true
            ;;
            -d | --dry-run )
                dry_run=true
            ;;
            -s | --stub )
                stub=true
            ;;
            -t | --test)
                test_upload="--repository testpypi"
            ;;
            -b | --build)
                build=true
            ;;
            * )
                args+=("$param")
            ;;
        esac
    done

    # Restore positional args
    set -- "${args[@]}"
}

function cleanup() {
    pushd "$workspace_path" || exit

    rm -rf build
    rm -rf dist

    popd || exit
}

function generate_stubs() {
    pushd "$workspace_path" || exit

    # check if pybind11-stubgen is installed
    if [[ ! $(pip3 show pybind11-stubgen) ]]; then
        echo "Missing pybind11-stubgen. Please install it with pip if you want to generate stubs"
        return
    fi
    rm -f pydlinear/_pydlinear.pyi pydlinear/_pydlinear.so
    pip3 install .
    pybind11-stubgen pydlinear --output-dir pydlinear/stubs
    mv pydlinear/stubs/pydlinear-stubs/_pydlinear/__init__.pyi pydlinear
    rm -rf pydlinear/stubs

    popd || exit
}

function build() {
    pushd "$workspace_path" || exit

    bazel build //pydlinear --config pydlinear

    popd || exit
}

function upload() {
    pushd "$workspace_path" || exit

    (pip3 show build > /dev/null && pip3 show twine >/dev/null) || (echo "Please install build and twine with pip first" && exit 1)
    python3 -m build
    python3 -m twine upload $test_upload dist/*

    popd || exit
}

# DESC: Main control flow
# ARGS: $@ (optional): Arguments provided to the script
# OUTS: None
function main() {
    script_init "$@"
    parse_args "$@"

    readonly workspace_path="$script_path/.."

    if [[ $cleanup = true ]]; then
        cleanup
        exit 0
    fi

    if [[ $build = true ]]; then
        build
    fi

    if [[ $stub = true ]]; then
        generate_stubs
    fi

    if [[ $dry_run = true ]]; then
        exit 0
    fi

    upload
}

# Invoke main with args if not sourced
if ! (return 0 2> /dev/null); then
    main "$@"
fi
