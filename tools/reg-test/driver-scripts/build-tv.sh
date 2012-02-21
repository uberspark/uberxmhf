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
