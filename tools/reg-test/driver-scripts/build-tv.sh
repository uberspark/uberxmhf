#!/bin/bash

# Immediately bail out if any errors are detected (non-zero exit
# status from a child process)
set -e

# Find the absolute path of this script
MY_PATH=`dirname "$0"`
MY_PATH=`( cd "$MY_PATH" && pwd )`

REPO_ROOT_RELPATH=../../..
REPO_ROOT_ABSPATH=`( cd "$MY_PATH/$REPO_ROOT_RELPATH" && pwd )`

# These are the relative & absolute paths of XMHF
XMHF_RELPATH=../../../xmhf
XMHF_ABSPATH=`( cd "$MY_PATH/$XMHF_RELPATH" && pwd )`

# and these are TrustVisor and tee-sdk's paths
TV_RELPATH=../../../trustvisor
TV_XMHF_RELPATH=../trustvisor
TV_ABSPATH=`( cd "$MY_PATH/$TV_RELPATH" && pwd )`
TEESDK_RELPATH=../../../tee-sdk
TEESDK_ABSPATH=`( cd "$MY_PATH/$TEESDK_RELPATH" && pwd )`
TESTPAL_RELPATH=../../../tee-sdk/examples/test
TESTPAL_ABSPATH=`( cd "$MY_PATH/$TESTPAL_RELPATH" && pwd )`

# and these are libbaremetal's paths
LIBBAREMETAL_RELPATH=../../../libbaremetal/src
LIBBAREMETAL_ABSPATH=`( cd "$MY_PATH/$LIBBAREMETAL_RELPATH" && pwd )`

# libtomcrypt
LIBTOMCRYPT_RELPATH=../../../third-party/libtomcrypt
LIBTOMCRYPT_ABSPATH=`( cd "$MY_PATH/$LIBTOMCRYPT_RELPATH" && pwd )`

# libtommath
LIBTOMMATH_RELPATH=../../../third-party/libtommath
LIBTOMMATH_ABSPATH=`( cd "$MY_PATH/$LIBTOMMATH_RELPATH" && pwd )`

# Temporary directory to place build results
TEMPROOT=`mktemp -d --tmpdir=/tmp build-tv.XXXXXXXXXX`
TEMPDIR=$TEMPROOT/tee-sdk
mkdir -p $TEMPDIR

# 0. Pull the latest source code.
pushd $REPO_ROOT_ABSPATH
# If anything besides untracked files (denoted by '??' at the
# beginning of the line; see 'git help status') exists, then bail out.
# That usually happens when one of us developers has been tinkering
# around and forgot to commit things.  Otherwise, the 'git clean' will
# clobber our work.
IS_DIRTY=`git status --porcelain | perl -n -e 'if ($_ !~ /^\?\?/) { print "DIRTY\n"; exit; }'`
if [ "$IS_DIRTY" == "DIRTY" ]; then
    echo "ERROR: working directory dirty. Did you forget to commit something?" >&2
    exit 1
fi
git clean -d -f -x .
#git pull

## 1. Build XMHF + TrustVisor

pushd $TV_ABSPATH
./autogen.sh
popd

pushd $XMHF_ABSPATH
./autogen.sh
./configure --prefix=$TEMPDIR --with-approot=$TV_XMHF_RELPATH --with-libbaremetalsrc=$LIBBAREMETAL_ABSPATH --with-libtomcryptsrc=$LIBTOMCRYPT_ABSPATH --with-libtommathsrc=$LIBTOMMATH_ABSPATH
make clean
make
#DESTDIR=$TEMPDIR make install
ls -l init-x86.bin hypervisor-x86.bin.gz

## 2. Install TrustVisor host development files
make install-dev

## 3. Install TrustVisor cross-compile development files
./configure --prefix=$TEMPDIR/i586-tsvc --with-approot=$TV_XMHF_RELPATH --with-libbaremetalsrc=$LIBBAREMETAL_ABSPATH
make install-dev

popd

# symlinks in /usr/lib32 for libcrypto.so and libssl.so
# embed output of `git svn info` into init-x86.bin somewhere

## 4. Build and install tee-sdk

# now trustvisor headers are in place and can build & install tee-sdk
pushd $TEESDK_ABSPATH
make PREFIX=$TEMPDIR
popd

# Now to build the examples/test PAL:
pushd $TESTPAL_ABSPATH
PATH=$PATH:$TEMPDIR/bin PKG_CONFIG_PATH=$TEMPDIR/lib/pkgconfig:/usr/lib/i386-linux-gnu/pkgconfig/ make clean
PATH=$PATH:$TEMPDIR/bin PKG_CONFIG_PATH=$TEMPDIR/lib/pkgconfig:/usr/lib/i386-linux-gnu/pkgconfig/ make
popd

rm -rf $TEMPDIR

echo -e "\nTRUSTVISOR BUILD COMPLETED SUCCESSFULLY\n"
