#/bin/bash

readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 || exit ; pwd -P )"
readonly dist_dir="$script_path/../dist"

# Build the inplp library using the debug configuration.
pushd "$script_path/.." > /dev/null || exit 1

rm -rf ${dist_dir}/*
mkdir -p ${dist_dir}

VERSION=$(git describe --tags --abbrev=0)
git archive --format=tar HEAD | xz > dlinear_${VERSION}.orig.tar.xz
tar -xvJf dlinear_${VERSION}.orig.tar.xz -C ${dist_dir}
cp -r package/debian ${dist_dir}

pushd ${dist_dir} > /dev/null || exit 1
dpkg-buildpackage --build=binary

popd > /dev/null || exit 1

popd > /dev/null || exit 1