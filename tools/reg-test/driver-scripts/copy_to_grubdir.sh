#!/bin/bash

set -e

# This script copies files to the LVM /boot partition for the
# specified test host, in the /grub subdirectory

if [ -z "$1" -o -z "$2" ] ; then
    echo "Usage: $0 hostname file1 file2 .. filen" 1>&2
    exit 1
fi

MAPPER_MOUNTS=`mount | grep mapper | wc -l`

if [ $MAPPER_MOUNTS -gt 0 ]; then
    echo "ERROR: Looks like some LVM filesystems are already mounted" 1>&2
    exit 1
fi

if [ `whoami` != "root" ]; then
    echo "ERROR: must be run as root!" 1>&2
    exit 1
fi

TESTHOSTNAME="$1"
# Drop hostname from arglist
shift

for file in "$@"; do
    if [ ! -e ${file} ]; then
        echo "ERROR: Source file $1 not found" 1>&2
        exit 1
    fi
done

TARGET=/mnt

echo "$0: Source files exist. Here goes!"
$DRYRUN losetup /dev/loop0 /dev/vg0/iscsi.slashboot.$TESTHOSTNAME
$DRYRUN kpartx -av /dev/loop0
$DRYRUN mount /dev/mapper/loop0p1 $TARGET
$DRYRUN cp -v $@ $TARGET/grub
$DRYRUN sync
$DRYRUN umount $TARGET
$DRYRUN kpartx -dv /dev/loop0
$DRYRUN losetup -d /dev/loop0

