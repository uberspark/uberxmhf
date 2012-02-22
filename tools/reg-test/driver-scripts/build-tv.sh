#!/bin/bash

# Immediately bail out if any errors are detected (non-zero exit
# status from a child process)
set -e

# Find the absolute path of this script
MY_PATH=`dirname "$0"`
MY_PATH=`( cd "$MY_PATH" && pwd )`

# These are the relative & absolute paths of EMHF
EMHF_RELPATH=../../../emhf/trunk/code
EMHF_ABSPATH=`( cd "$MY_PATH/$EMHF_RELPATH" && pwd )`

# and these are TrustVisor and tee-sdk's paths
TV_RELPATH=../../../trustvisor/trunk/code
TEESDK_RELPATH=../../../tee-sdk/trunk
TESTPAL_RELPATH=../../../tee-sdk/trunk/examples/test

# Temporary directory to place build results
TEMPDIR=/tmp/build/tee-sdk
rm -rf $TEMPDIR
mkdir -p $TEMPDIR

pushd $EMHF_ABSPATH

## 1. Build TrustVisor

make clean
#git svn rebase
autoreconf -i
./configure --prefix=$TEMPDIR --with-approot=$TV_RELPATH
make clean
make
#DESTDIR=$TEMPDIR make install
ls -l init-x86.bin hypervisor-x86.bin.gz

## 2. Install TrustVisor host development files
make install-dev

## 3. Install TrustVisor cross-compile development files
./configure --prefix=$TEMPDIR/i586-tsvc --with-approot=$TV_RELPATH
make install-dev

popd

# symlinks in /usr/lib32 for libcrypto.so and libssl.so
# embed output of `git svn info` into init-x86.bin somewhere

## 4. Build and install tee-sdk

# now trustvisor headers are in place and can build & install tee-sdk
pushd $TEESDK_RELPATH
make PREFIX=$TEMPDIR
popd

# Now to build the examples/test PAL:
pushd $TESTPAL_RELPATH
PATH=$PATH:$TEMPDIR/bin PKG_CONFIG_PATH=$TEMPDIR/lib/pkgconfig make clean
PATH=$PATH:$TEMPDIR/bin PKG_CONFIG_PATH=$TEMPDIR/lib/pkgconfig make
popd

echo -e "\nTRUSTVISOR BUILD COMPLETED SUCCESSFULLY\n"
