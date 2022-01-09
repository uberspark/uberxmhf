#!/bin/bash

set -xe

MAKE_ARGS=""

if [ "$1" == "x86" ]; then
	MAKE_ARGS="${MAKE_ARGS} CC=i686-linux-gnu-gcc"
	MAKE_ARGS="${MAKE_ARGS} LD=i686-linux-gnu-ld"
else if [ "$1" == "x86_64" ]; then
	MAKE_ARGS="${MAKE_ARGS}"
else
	echo '$1 incorrect, should be x86 or x86_64'; exit 1
fi; fi

cd hypapps/trustvisor/pal_demo
make "${MAKE_ARGS}"

