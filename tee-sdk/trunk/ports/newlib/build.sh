#!/bin/sh

mkdir build
mkdir install

cd build

STRIP_FOR_TARGET=strip RANLIB_FOR_TARGET=ranlib OBJDUMP_FOR_TARGET=objdump NM_FOR_TARGET=nm LD_FOR_TARGET=ld AS_FOR_TARGET=as AR_FOR_TARGET=ar CC_FOR_TARGET=cc GCC_FOR_TARGET=gcc ../newlib-1.19.0/configure --target=i586 --disable-multilib --prefix=`pwd`/../install

make
make install