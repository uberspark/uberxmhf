#!/bin/sh

if [ -z "$HOST" ]
then
	HOST=i586-tsvc
fi

if [ -z "$PREFIX" ]
then
	PREFIX=/usr/local/$HOST/usr
fi

if [ -z "$CC" ]
then
	CC=${HOST}-cc
fi
export CC

if [ -z "$RANLIB" ]
then
	RANLIB=${HOST}-ranlib
fi
export RANLIB

if [ -z "$AR" ]
then
	AR=${HOST}-ar
fi
export AR

CFLAGS="-DOPENSSL_NO_DGRAM -DOPENSSL_NO_SOCK -UWINDOWS -UWIN32 -U_WIN32 -DOPENSSL_SYS_LINUX"

cd openssl-1.0.0d
./Configure tsvc-elf --prefix="$PREFIX" no-threads no-zlib no-shared no-sse2 no-dso no-hw no-asm $CFLAGS
make
sudo make install

