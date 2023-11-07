#!/bin/bash

set -xe
if [ "$1" == "i386" ]; then
	export SUBARCH="i386"
	export SA_x86_x64="x86"
	export SA_32_64="32"
else if [ "$1" == "amd64" ]; then
	export SUBARCH="amd64"
	export SA_x86_x64="x64"
	export SA_32_64="64"
else
	echo 'Error: unknown subarch'; exit 1
fi; fi

export qemu_image_back="debian11${SA_x86_x64}.qcow2"
export qemu_image="debian11${SA_x86_x64}-c.qcow2"

