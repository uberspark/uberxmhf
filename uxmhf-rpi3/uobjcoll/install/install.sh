#!/bin/bash

# installation script
# author: amit vasudevan <amitvasudevan@acm.org>

set -e

if [[ $# -ne 1 ]]; then
    echo "usage: install.sh <path-to-kernel-image-file>"
    exit 1
fi

KERNEL_IMAGE=$1
UOBJCOLL_IMAGE=../_build/uobjcoll.exe.flat

KERNEL_IMAGE_SIZE=`stat -c %s ${KERNEL_IMAGE}`
UOBJCOLL_IMAGE_SIZE=`stat -c %s ${UOBJCOLL_IMAGE}`

# TBD parse sentinel manifest to get this
INITMETHOD_SENTINEL_SIZE=4096


INITMETHOD_SENTINEL_PLUS_KERNEL_IMAGE_SIZE=`echo "$KERNEL_IMAGE_SIZE + $INITMETHOD_SENTINEL_SIZE" | bc`
UOBJCOLL_SANS_INITMETHOD_SENTINEL_SIZE=`echo "$UOBJCOLL_IMAGE_SIZE - $INITMETHOD_SENTINEL_PLUS_KERNEL_IMAGE_SIZE" | bc`

echo $KERNEL_IMAGE_SIZE
echo $UOBJCOLL_IMAGE_SIZE
echo $INITMETHOD_SENTINEL_SIZE
echo $INITMETHOD_SENTINEL_PLUS_KERNEL_IMAGE_SIZE
echo $UOBJCOLL_SANS_INITMETHOD_SENTINEL_SIZE

# pare away temp files
dd if=${UOBJCOLL_IMAGE} of=temp_01.bin bs=4096 count=1
dd if=${UOBJCOLL_IMAGE} skip=${INITMETHOD_SENTINEL_PLUS_KERNEL_IMAGE_SIZE} count=${UOBJCOLL_SANS_INITMETHOD_SENTINEL_SIZE} of=temp_03.bin iflag=skip_bytes,count_bytes

# generate image
cat temp_01.bin ${KERNEL_IMAGE} temp_03.bin > uxmhf-rpi3.img

# remove temp files
rm -f temp_01.bin
rm -f temp_03.bin



