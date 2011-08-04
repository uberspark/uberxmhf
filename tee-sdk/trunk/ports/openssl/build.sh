#!/bin/sh

export CC=i586-tsvc-cc
export LD=i586-tsvc-ld
PREFIX=/usr/local/i586-tsvc/usr
CFLAGS="-DOPENSSL_NO_DGRAM -DOPENSSL_NO_SOCK"

cd openssl-1.0.0d
./Configure cc --prefix="$PREFIX" no-threads no-zlib no-shared no-sse2 no-dso no-hw $CFLAGS
make
make install
