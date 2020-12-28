#!/bin/bash

set -e

LOADER_IMAGE=../_build/uberspark/loaders/baremetal/x86_32/grub-legacy/_build/loader.exe.flat
UOBJCOLL_IMAGE=../_build/uobjcoll.exe.flat

LOADER_IMAGE_SIZE=`stat -c %s ${LOADER_IMAGE}`
UOBJCOLL_IMAGE_SIZE=`stat -c %s ${UOBJCOLL_IMAGE}`

echo $LOADER_IMAGE_SIZE
echo $UOBJCOLL_IMAGE_SIZE

# generate image
cat ${LOADER_IMAGE} ${UOBJCOLL_IMAGE} > uxmhf.img
gzip -c ./uxmhf.img > ./xmhf-x86-vmx-x86pc.bin.gz

# remove temp files
rm -f uxmhf.img


