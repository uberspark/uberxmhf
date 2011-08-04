#!/bin/sh

NEWLIBINC=`pwd`/../newlib/install/i586-tsvc/include

CCINC=`gcc --print-file-name=include`
CFLAGS=`pkg-config --cflags tee-sdk-svc tee-sdk-svc-tv`"-nostdinc -fno-builtin -I$NEWLIBINC -I$CCINC -I$CCINC-fixed -DOPENSSL_NO_DGRAM -DOPENSSL_NO_SOCK"
PREFIX=`pwd`/install

cd openssl-1.0.0d
./Configure cc --prefix="$PREFIX" no-threads no-zlib no-shared no-sse2 no-dso no-hw no-ui $CFLAGS
make
make install
