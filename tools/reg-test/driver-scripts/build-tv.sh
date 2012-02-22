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

# and these are TrustVisor's paths
TV_RELPATH=../../../trustvisor/trunk/code
TV_ABSPATH=`( cd "$MY_PATH/$TV_RELPATH" && pwd )`

pushd $EMHF_ABSPATH

make clean
git svn rebase
autoreconf
./configure --with-approot=$TV_ABSPATH
make clean
make

ls -l init-x86.bin hypervisor-x86.bin.gz

echo -e "\nTRUSTVISOR BUILD COMPLETED SUCCESSFULLY\n"

# embed output of `git svn info` into init-x86.bin somewhere


# configure TV with cross compiler prefix
cd ../../../trustvisor/trunk/code
autoreconf
./configure --prefix=/home/driver/tmp/tee-sdk/i586-tsvc
# configure EMHF with cross compiler prefix and approot
cd ../../../emhf/trunk/code
./configure --prefix=/home/driver/tmp/tee-sdk/i586-tsvc --with-approot=/home/driver/hyp.git/trustvisor/trunk/code
make install-dev

# repeat with regular prefix (not cross compiler prefix)
cd ../../../trustvisor/trunk/code
./configure --prefix=/home/driver/tmp/tee-sdk
cd ../../../emhf/trunk/code
./configure --prefix=/home/driver/tmp/tee-sdk --with-approot=/home/driver/hyp.git/trustvisor/trunk/code

# now trustvisor headers are in place and can build & install tee-sdk
cd ../../../tee-sdk/trunk
make PREFIX=/home/driver/tmp/tee-sdk

# Now to build the examples/test PAL:
PATH=$PATH:/home/driver/tmp/tee-sdk/bin PKG_CONFIG_PATH=~/tmp/tee-sdk/lib/pkgconfig make clean
PATH=$PATH:/home/driver/tmp/tee-sdk/bin PKG_CONFIG_PATH=~/tmp/tee-sdk/lib/pkgconfig make

