#!/usr/bin/env bash
# Script template author: Michel VONGVILAY (https://www.uxora.com)
# License: CC-BY-SA Creative Commons License
#================================================================
# HEADER
#================================================================
#% SYNOPSIS
#+    ${SCRIPT_NAME} [-h] [-v] [-d] [-o] [-c] [-p precision] operation [filename]
#%
#% DESCRIPTION
#%    Run dLinear's LP or QF_LRA benchmarks.
#%    There are three operations: lp, qf_lra, and install.
#%    The install operation installs dLinear from the ppa repository. Must be run as root.
#%    The lp operation downloads the LP benchmarks, then runs dLinear on the specified file.
#%    The qf_lra operation downloads the QF_LRA benchmarks, then runs dLinear on the specified file.
#%    If filename is 'all', dLinear will run on all benchmarks in the folder.
#%    Keep in mind that this may be extremely time-consuming.
#%    dLinear will run in complete mode unless the -p flag is set.
#%
#% OPTIONS
#%    -d, --download                Download the benchmark files without running dLinear
#%    -o, --override                Override previous downloads if they exist
#%    -p, --precision               Use dLinear in delta-complete mode with the given precision
#%    -c, --csv                     Output results in csv format
#%    -h, --help                    Print this help
#%    -v, --version                 Print script information
#%
#% EXAMPLES
#%    sudo ./${SCRIPT_NAME} install         # Install dLinear
#%    ./${SCRIPT_NAME} lp all               # Run dLinear on all LP benchmarks
#%    ./${SCRIPT_NAME} qf_lra -d            # Download QF_LRA benchmarks
#%    ./${SCRIPT_NAME} lp --csv -p 1 afiro  # Run dLinear on the afiro.mps file in csv format with delta = 1
#%
#================================================================
#- IMPLEMENTATION
#-    version         ${SCRIPT_NAME} 0.1.0
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
ERROR="ERROR:"
WARNING="WARNING:"
INFO="INFO:"

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
    readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
    readonly script_dir="$(dirname ${BASH_SOURCE[0]})"
    readonly script_name="$(basename "${BASH_SOURCE[0]}")"
    readonly ta_none="$(tput sgr0 2> /dev/null || true)"
    readonly script_headsize=$(head -200 ${0} |grep -n "^# END_OF_HEADER" | cut -f1 -d:)
}

# DESC: Verify the user wants to continue asking (y/n)
# ARGS: $1: Message to display
function confirm() {
    local message="$1"
    if [[ -z "${yes}" ]]; then
        read -p "${message}${ta_bold}Continue?${ta_none} ${ta_uscore}[y/N]${ta_none} " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            >&2 echo "Operation aborted by user"
            exit 1
        fi
    fi
}

function file_exists() {
    if [ ! -f "$1" ]; then
        >&2 echo "${ERROR} File not found: $1"
        exit 1
    fi
}

# DESC: Initialise colour variables
# ARGS: None
# OUTS: Read-only variables with ANSI control codes
# NOTE: If --no-color was set the variables will be empty. The output of the
#       $ta_none variable after each tput is redundant during normal execution,
#       but ensures the terminal output isn't mangled when running with xtrace.
function color_init() {
    # Text attributes
    readonly ta_bold="$(tput bold 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly ta_uscore="$(tput smul 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly ta_blink="$(tput blink 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly ta_reverse="$(tput rev 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly ta_conceal="$(tput invis 2> /dev/null || true)"
    printf '%b' "$ta_none"

    # Foreground codes
    readonly fg_black="$(tput setaf 0 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly fg_blue="$(tput setaf 4 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly fg_cyan="$(tput setaf 6 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly fg_green="$(tput setaf 2 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly fg_magenta="$(tput setaf 5 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly fg_red="$(tput setaf 1 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly fg_white="$(tput setaf 7 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly fg_yellow="$(tput setaf 3 2> /dev/null || true)"
    printf '%b' "$ta_none"

    # Background codes
    readonly bg_black="$(tput setab 0 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly bg_blue="$(tput setab 4 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly bg_cyan="$(tput setab 6 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly bg_green="$(tput setab 2 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly bg_magenta="$(tput setab 5 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly bg_red="$(tput setab 1 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly bg_white="$(tput setab 7 2> /dev/null || true)"
    printf '%b' "$ta_none"
    readonly bg_yellow="$(tput setab 3 2> /dev/null || true)"
    printf '%b' "$ta_none"

    ERROR="${ta_bold}${fg_red}ERROR:${ta_none}"
    WARNING="${ta_bold}${fg_yellow}WARNING:${ta_none}"
    INFO="${ta_bold}${fg_green}INFO:${ta_none}"
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
    mode_flag="-c"

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
            -nc | --no-color)
                no_color=1
            ;;
            -p | --precision)
                mode_flag="-p $1"
                shift
            ;;
            -c | --csv )
                readonly csv="--csv"
            ;;
            -d | --download )
                readonly download=1
            ;;
            -o | --optional_param )
                readonly override=1
            ;;
            * )
                args+=("$param")
            ;;
        esac
    done

    # Restore positional args
    set -- "${args[@]}"

    if [[ -z "${no_color}" ]]; then
        color_init
    fi

    # set positionals to vars
    readonly operation="${args[0]}"
    readonly filename="${args[1]}"

    # Validate required args
    if [[ -z "operation" ]]; then
        >&2 echo "${ERROR} Missing required argument 'operation'"
        usage
        exit 1;
    elif [ "$operation" != "lp" ] && [ "$operation" != "qf_lra" ] && [ "$operation" != "install" ]; then
        >&2 echo "${ERROR} Invalid argument 'operation': ${operation}. Must be one of { lp | qf_lra | install }"
        usage
        exit 1;
    fi

    if [ -z "${filename}" ] && [ "$operation" != "install" ]; then
        >&2 echo "${ERROR} Missing required argument 'filename'"
        usage
        exit 1;
    fi
}

function install() {
    confirm "This operation will install dLinear from the ppa repository. "
    # Check if running as root
    if [ "$EUID" -ne 0 ]; then
        >&2 echo "${ERROR} This operation must be run as root (sudo)"
        exit 1
    fi
#    add-apt-repository ppa:dlinear/dlinear
    echo ${INFO} "Updating package list"
    apt-get update -y -qq
#    apt-get install dlinear
}

function download_lp() {
  # Check if folder exists
  if [ -d "lp" ] && [ -z "${override}" ]; then
    echo "${INFO} lp folder detected. Skipping download..."
    return
  fi
  echo "${INFO} Downloading lp benchmarks"
  wget -m -np https://www.netlib.org/lp/ # Creates a www.netlib.org folder
  rm -rf "www.netlib.org/lp/generators"
  find "www.netlib.org" -name "readme" -delete
  find "www.netlib.org" -name "*.html" -delete
  find "www.netlib.org" -name "*.txt" -delete
  find "www.netlib.org" -name "*.ps" -delete
  find "www.netlib.org" -name "*.exe" -delete
  find "www.netlib.org" -name "stocfor3*" -delete
  find "www.netlib.org" -name "truss" -delete
  find "www.netlib.org" -name "minos" -delete
  find "www.netlib.org" -name "ascii" -delete
  find "www.netlib.org" -name "*.f" -delete
  find "www.netlib.org" -name "*.src" -delete
  find "www.netlib.org" -name "changes" -delete
  find "www.netlib.org" -name "*.gz" -exec gzip -dkf {} \;
  find "www.netlib.org" -name "*.gz" -delete
  find "www.netlib.org" -name "emps.c" -exec mv {} . \;
  gcc -o emps emps.c
  find "www.netlib.org" -type f -exec bash -c "eval ./emps -1 -b -m {} > {}.mps" \;
  mkdir -p lp
  find "www.netlib.org" -name "*.mps" -exec mv {} lp \;
  rm -rf "www.netlib.org"
  rm -f emps
  rm emps.c
}

function download_qf_lra() {
  # Check if folder exists
  if [ -d "qf_lra" ] && [ -z "${override}" ]; then
    echo "${INFO} qf_lra folder detected. Skipping download..."
    return
  fi
  echo "${INFO} Downloading qf_lra benchmarks"
  curl https://zenodo.org/records/11061097/files/QF_LRA.tar.zst -o QF_LRA.tar.zst
  tar -xf QF_LRA.tar.zst
  rm QF_LRA.tar.zst
  mkdir -p qf_lra
  find "non-incremental" -name "*.smt2" -exec mv {} qf_lra \;
  rm -r non-incremental
}

function lp() {
    download_lp
    if [[ -n "${download}" ]]; then
        echo "${INFO} Stopping here as --download flag was set"
        return
    fi
    echo "${INFO} Running dLinear on lp benchmarks"
    if [ "$filename" == "all" ]; then
        find lp -name "*.mps" -exec dlinear -t $csv $mode_flag {} \;
    else
        file_exists "lp/$(basename $filename).mps"
        dlinear -t $csv $mode_flag --enforce-check-sat "lp/$(basename $filename).mps"
    fi
}

function qf_lra() {
    download_qf_lra
    if [[ -n "${download}" ]]; then
        echo "${INFO} Stopping here as --download flag was set"
        return
    fi
    echo "${info} Running dLinear on qf_lra benchmarks"
    if [ "$filename" == "all" ]; then
        find qf_lra -name "*.smt2" -exec dlinear -t $csv $mode_flag {} \;
    else
        file_exists "qf_lra/$(basename $filename).smt2"
        dlinear -t $csv $mode_flag "qf_lra/$(basename $filename).smt2"
    fi
}

# DESC: Main control flow
# ARGS: $@ (optional): Arguments provided to the script
# OUTS: None
function main() {
    script_init "$@"
    parse_args "$@"
    PATH="$PATH:$(pwd)/../bazel-bin/dlinear"
  case "$operation" in
        install)
            install
        ;;
        lp)
            lp
        ;;
        qf_lra)
            qf_lra
        ;;
    esac
}

# Invoke main with args if not sourced
if ! (return 0 2> /dev/null); then
    main "$@"
fi