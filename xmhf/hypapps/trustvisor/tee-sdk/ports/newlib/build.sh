#!/bin/sh

rm -rf build install
mkdir build
mkdir install

cd build

CFLAGS="-U__CYGWIN__ -UWIN32 -m32"
#CFLAGS=`pkg-config --cflags tee-sdk-svc tee-sdk-svc-tv`

#CFLAGS="$CFLAGS" STRIP_FOR_TARGET=strip RANLIB_FOR_TARGET=ranlib OBJDUMP_FOR_TARGET=objdump NM_FOR_TARGET=nm LD_FOR_TARGET=ld AS_FOR_TARGET=as AR_FOR_TARGET=ar CC_FOR_TARGET=cc GCC_FOR_TARGET=gcc ../newlib-1.19.0/configure --target=i586-tsvc --enable-languages=c --with-newlib --disable-multilib --prefix=`pwd`/../install
if [ -z $HOST ]
then
	HOST=i586-tsvc
fi

if [ -z $PREFIX ]
then
	PREFIX=/usr/local
fi

CFLAGS=$CFLAGS ../newlib-1.19.0/configure --target=${HOST} --enable-languages=c --with-newlib --disable-multilib --prefix=$PREFIX

make
make install

