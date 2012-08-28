#!/bin/bash

set -e

# This script copies files (provided as args) to all of the different /boot partitions for test hosts
MAPPER_MOUNTS=`mount | grep mapper | wc -l`

if [ $MAPPER_MOUNTS -gt 0 ]; then
    echo "ERROR: Looks like some LVM filesystems are already mounted" 1>&2
    exit 1
fi

for file in "$@"; do
    if [ ! -e ${file} ]; then
        echo "ERROR: Source file $1 not found" 1>&2
        exit 1
    fi
done

TARGET=/mnt

echo "$0: Source files exist. Here goes!"
for i in /dev/vg0/iscsi.slashboot.* ; do 
    echo "*** Copying $1 to $i ***"

    $DRYRUN losetup /dev/loop0 $i
    $DRYRUN kpartx -av /dev/loop0
    $DRYRUN mount /dev/mapper/loop0p1 $TARGET
    $DRYRUN cp -v $@ $TARGET
    $DRYRUN sync
    $DRYRUN umount $TARGET
    $DRYRUN kpartx -dv /dev/loop0
    $DRYRUN losetup -d /dev/loop0
    #break
done

for i in /dev/vg0/oneiric_rootfs /dev/vg0/lucid_rootfs /dev/vg0/precise_rootfs; do
    echo "*** Copying $1 to $i ***"
    #break
    $DRYRUN losetup /dev/loop0 $i
    $DRYRUN kpartx -av /dev/loop0
    $DRYRUN mount /dev/mapper/loop0p1 $TARGET
    $DRYRUN cp -v $@ $TARGET/boot
    $DRYRUN sync
    $DRYRUN umount $TARGET
    $DRYRUN kpartx -dv /dev/loop0
    $DRYRUN losetup -d /dev/loop0
done
