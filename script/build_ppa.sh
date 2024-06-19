#/bin/bash

readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 || exit ; pwd -P )"
readonly dist_dir="$script_path/../dist"
readonly build=${1:-source}

pushd "$script_path/.." > /dev/null || exit 1

rm -rf ${dist_dir}/*
mkdir -p ${dist_dir}
bazel build --enable_fpic_build //package
cp bazel-bin/package/package.tar.gz ${dist_dir}
cp -r package/debian ${dist_dir}

pushd ${dist_dir} > /dev/null || exit 1

version=$(dpkg-parsechangelog --show-field Version | cut -f1 -d'-')
tar -cJf ../dlinear_${version}.orig.tar.xz package.tar.gz
dpkg-buildpackage --build=${build}

popd > /dev/null || exit 1

popd > /dev/null || exit 1

