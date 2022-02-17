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
else if [ "$1" == "all" ]; then
	build_and_move () {
		"$1" "$2" "$3"
		for i in hypapps/trustvisor/pal_demo/{main,test,test_args}; do
			mv "${i}$5" "${i}$4$5"
		done
	}
	build_and_move "$0" linux   x86    32 ""
	build_and_move "$0" linux   x86_64 64 ""
	build_and_move "$0" windows x86    32 ".exe"
	build_and_move "$0" windows x86_64 64 ".exe"
	exit
else
	echo '$1 incorrect, should be windows or linux'; exit 1
fi; fi; fi

cd hypapps/trustvisor/pal_demo
make clean
make ${MAKE_ARGS}

