#!/bin/bash

export CC=armcc
export IGNORE_SPEED=1 # armcc doesn't understand -funroll-loops etc.
export EXTRALIBS="-ltommath" # use libtommath. not most performant, but very portable
CFLAGS="-DLTM_DESC" # include libtommath descriptor
CFLAGS+=" -DUSE_LTM" # use libtommath descriptor in any compiled executables
CFLAGS+=" -D_WCHAR_T_DEFINED" # prevent from trying to redefine wchar_t
CFLAGS+=" -I/home/jnewsome/src/libtommath" # point to libtommath headers
CFLAGS+=" --cpu=Cortex-A8 --fpu=None --fpmode=none" # CPU spec
export CFLAGS
export LDFLAGS="-L/home/jnewsome/src/libtommath" # point to libtommath libs
make

