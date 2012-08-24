#!/bin/bash

export TARGET=/mnt

for i in test-6555b test-e8100 creeper pratt; do 
    losetup /dev/loop0 /dev/vg0/iscsi.slashboot.$i
    kpartx -av /dev/loop0
    mount /dev/mapper/loop0p1 $TARGET

    echo
    echo "HOST $i grub/default file"
    ls -l $TARGET/grub/default
    hd $TARGET/grub/default
    echo "HOST $i grub/menu.lst file"
    ls -l $TARGET/grub/menu.lst
    cat $TARGET/grub/menu.lst
    mount | grep mapper

    umount $TARGET
    kpartx -dv /dev/loop0
    losetup -d /dev/loop0
done
