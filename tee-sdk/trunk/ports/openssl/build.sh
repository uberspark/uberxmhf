#!/bin/sh

NEWLIBINC=`pwd`/../newlib/install/i586-tsvc/include

CCINC=`gcc --print-file-name=include`
CFLAGS=`pkg-config --cflags tee-sdk-svc tee-sdk-svc-tv`"-nostdinc -fno-builtin -I$NEWLIBINC -I$CCINC -I$CCINC-fixed"
PREFIX=`pwd`/install

cd openssl-1.0.0d
./config --prefix="$PREFIX" no-threads no-zlib no-shared no-sse2 $CFLAGS
make
make install
