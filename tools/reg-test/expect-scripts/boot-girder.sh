#!/bin/bash

# This script contains the necessary bootloader configuration for the
# test host 'girder' (HP ProBook 6555b laptop with AMD CPU).  These
# variables are set before invoking an 'expect' script that can handle
# the interactive session with grub via a serial port.

# TODO: Cope with amtterm.

export FIRST_ROOT='root (hd0,0)'
export FIRST_KERNEL='kernel /boot/init-x86.bin serial=115200,8n1,0x3f8'
export FIRST_MOD1='module /boot/hypervisor-x86.bin.gz'
export FIRST_MOD2='modulenounzip (hd0)+1'
# On an AMD host such as girder this is a dummy module and is not used
export FIRST_MOD3='module /boot/i5_i7_DUAL_SINIT_18.BIN'

export SECOND_ROOT='uuid e62ba4c2-87d2-4b42-b66d-dabf9af0c68c'
export SECOND_KERNEL='kernel /boot/vmlinuz-2.6.32.26+drm33.12emhf-jm1 root=UUID=e62ba4c2-87d2-4b42-b66d-dabf9af0c68c ro ip=dhcp ISCSI_INITIATOR=iqn.2012-02.com.nfsec:01:643150805036 ISCSI_TARGET_NAME=iqn.2012-01.com.nfsec:lucid_rootfs ISCSI_TARGET_IP=10.0.0.1 ISCSI_TARGET_PORT=3260 aufs=tmpfs'
export SECOND_MOD1='initrd /boot/initrd.img-2.6.32.26+drm33.12emhf-jm1'

./grub-generic.exp ttyS0

