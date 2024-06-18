#/bin/bash

readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 || exit ; pwd -P )"
readonly dist_dir="$script_path/../dist"

# Build the inplp library using the debug configuration.
pushd "$script_path/.." > /dev/null || exit 1

rm -rf ${dist_dir}/*
mkdir -p ${dist_dir}

VERSION=$(git describe --tags --abbrev=0)
git archive --format=tar HEAD | xz > dlinear_${VERSION}.orig.tar.xz
wget https://github.com/bazelbuild/bazel/releases/download/7.1.1/bazel-7.1.1-linux-x86_64 -O ${dist_dir}/bazel
chmod +x ${dist_dir}/bazel
tar -xvJf dlinear_${VERSION}.orig.tar.xz -C ${dist_dir}
cp -r package/debian ${dist_dir}

pushd ${dist_dir} > /dev/null || exit 1


bazel fetch //package:debian
bazel_out=$(bazel info output_base)
ln -s "${bazel_out}" bazel_out
tar -cJf dlinear_${VERSION}.orig.tar.xz --dereference bazel dlinear MODULE.bazel MODULE.bazel.lock third_party tools BUILD.bazel bazel_out
mv dlinear_${VERSION}.orig.tar.xz ..

dpkg-buildpackage --build=source

popd > /dev/null || exit 1

popd > /dev/null || exit 1