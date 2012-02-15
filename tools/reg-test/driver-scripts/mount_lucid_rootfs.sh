#!/bin/bash

export TARGET=/mnt

losetup /dev/loop0 /dev/vg0/lucid_rootfs
kpartx -av /dev/loop0
mount /dev/mapper/loop0p1 $TARGET
mount -o bind /dev $TARGET/dev
mount -o bind /sys $TARGET/sys
mount -o bind /proc $TARGET/proc

