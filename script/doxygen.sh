#/bim/bash

readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 || exit ; pwd -P )"

# Build the inplp library using the debug configuration.
pushd "$script_path/.." > /dev/null || exit 1

rm -rf docs/out
doxygen docs/Doxyfile

popd > /dev/null || exit 1
