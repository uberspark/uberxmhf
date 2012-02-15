#!/bin/bash

export TARGET=/mnt

umount $TARGET/proc
umount $TARGET/sys
umount $TARGET/dev
umount $TARGET

kpartx -dv /dev/loop0
losetup -d /dev/loop0 
