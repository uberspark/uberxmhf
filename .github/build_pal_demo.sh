#!/bin/bash

set -xe

MAKE_ARGS=""

if [ "$1" == "windows" ]; then
	MAKE_ARGS="${MAKE_ARGS} WINDOWS=y"
	if [ "$2" == "x86" ]; then
		MAKE_ARGS="${MAKE_ARGS} CC=i686-w64-mingw32-gcc"
		MAKE_ARGS="${MAKE_ARGS} LD=i686-w64-mingw32-ld"
	else if [ "$2" == "x86_64" ]; then
		MAKE_ARGS="${MAKE_ARGS} CC=x86_64-w64-mingw32-gcc"
		MAKE_ARGS="${MAKE_ARGS} LD=x86_64-w64-mingw32-ld"
	else
		echo '$2 incorrect, should be x86 or x86_64'; exit 1
	fi; fi
else if [ "$1" == "linux" ]; then
	if [ "$2" == "x86" ]; then
		MAKE_ARGS="${MAKE_ARGS} CC=i686-linux-gnu-gcc"
		MAKE_ARGS="${MAKE_ARGS} LD=i686-linux-gnu-ld"
	else if [ "$2" == "x86_64" ]; then
		MAKE_ARGS="${MAKE_ARGS}"
	else
		echo '$2 incorrect, should be x86 or x86_64'; exit 1
	fi; fi
else
	echo '$1 incorrect, should be windows or linux'; exit 1
fi; fi

cd hypapps/trustvisor/pal_demo
make clean
make ${MAKE_ARGS}

