#!/bin/bash

# This script contains the necessary bootloader configuration for the
# test host 'girder' (HP ProBook 6555b laptop with AMD CPU).  These
# variables are set before invoking an 'expect' script that can handle
# the interactive session with grub via a serial port.

# TODO: Cope with amtterm instead of a real serial port.

# Values that are actually expected to change across test hosts:
# 1. SINIT module is chipset-dependent on Intel hosts
# 2. ISCSI_INITIATOR should be unique per test host (currently it is 
#    unique because of a suffix containing that test host's ethernet MAC 
#    address)
# 3. hostname= variable (currently ignored by test Linux environment)
# 4. The actual kernel version itself, if we want to test multiple versions

export FIRST_ROOT='root (hd0,0)'
export FIRST_KERNEL='kernel /boot/init-x86.bin serial=115200,8n1,0x3f8'
export FIRST_MOD1='module /boot/hypervisor-x86.bin.gz'
export FIRST_MOD2='modulenounzip (hd0)+1'
# On an AMD host such as girder this is a dummy module and is not used
export FIRST_MOD3='module /boot/i5_i7_DUAL_SINIT_18.BIN'

# lucid (Ubuntu 10.04 LTS)
#export SECOND_ROOT='uuid e62ba4c2-87d2-4b42-b66d-dabf9af0c68c'
#export SECOND_KERNEL='kernel /boot/vmlinuz-2.6.32.26+drm33.12emhf-jm1 root=UUID=e62ba4c2-87d2-4b42-b66d-dabf9af0c68c ro ip=dhcp hostname=girder ISCSI_INITIATOR=iqn.2012-02.com.nfsec:01:643150805036 ISCSI_TARGET_NAME=iqn.2012-01.com.nfsec:lucid_rootfs ISCSI_TARGET_IP=10.0.0.1 ISCSI_TARGET_PORT=3260 aufs=tmpfs'
#export SECOND_MOD1='initrd /boot/initrd.img-2.6.32.26+drm33.12emhf-jm1'

# oneiric (Ubuntu 11.10)
export SECOND_ROOT='uuid ad60f8ff-e0ca-4294-a7d4-9c07da18365b'
export SECOND_KERNEL='kernel /boot/vmlinuz-3.0.4-jm2 root=UUID=ad60f8ff-e0ca-4294-a7d4-9c07da18365b ro ip=dhcp hostname=girder ISCSI_INITIATOR=iqn.2012-02.com.nfsec:01:643150805036 ISCSI_TARGET_NAME=iqn.2012-01.com.nfsec:oneiric_rootfs ISCSI_TARGET_IP=10.0.0.1 ISCSI_TARGET_PORT=3260 aufs=tmpfs'
export SECOND_MOD1='initrd /boot/initrd.img-3.0.4-jm2'

# If it has been power-cycled and we want to Wake-on-Lan:
# (and actually, if the machine is already up, this is harmless)
etherwake 64:31:50:80:40:b8

# See 8x serial cable number <-> ttySx mapping at
# https://plover.pdl.cmu.local/projects/emhf/wiki/Regression_Testing_Ideas
./grub-generic.exp serial ttyS5

