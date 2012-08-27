#!/bin/bash

export TARGET=/mnt

if [ -z "$1" ]; then
    echo "Usage: $0 [filesystem image]" 2>&1
    echo "   ex: $0 /dev/vg0/precise_rootfs" 2>&1
    exit 65
fi

losetup /dev/loop0 "$1"
kpartx -av /dev/loop0
mount /dev/mapper/loop0p1 $TARGET
#mount -o bind /dev $TARGET/dev
#mount -o bind /sys $TARGET/sys
#mount -o bind /proc $TARGET/proc

