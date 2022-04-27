#!/bin/bash

mkdir -p ~/mnt/pi-boot
mkdir -p ~/mnt/pi-root
mount /dev/sdb1 ~/mnt/pi-boot
mount /dev/sdb2 ~/mnt/pi-root
cp uxmhf-rpi3-staging/uhcalltest ~/mnt/pi-root/home/pi/.
cp uxmhf-rpi3-staging/uhcallkmod.ko ~/mnt/pi-root/home/pi/.
cp uxmhf-rpi3-staging/uxmhf-rpi3.img ~/mnt/pi-boot/.
cp uxmhf-rpi3-staging/config.txt ~/mnt/pi-boot/.
sed -i 's/$/ loglevel=8 memblock=debug dwc_otg.fiq_enable=0 dwc_otg.fiq_fsm_enable=0/' ~/mnt/pi-boot/cmdline.txt
cp uxmhf-rpi3-staging/boot/* ~/mnt/pi-boot/.
mkdir -p ~/mnt/pi-boot/overlays
cp -R uxmhf-rpi3-staging/overlays/* ~/mnt/pi-boot/overlays.
cp uxmhf-rpi3-staging/kernel7.img ~/mnt/pi-boot/.
mkdir -p ~/mnt/pi-root/lib/firmware
cp -R uxmhf-rpi3-staging/mod_install/lib/firmware/* ~/mnt/pi-root/lib/firmware/.
mkdir -p ~/mnt/pi-root/lib/modules/4.4.50-v7+
cp -R uxmhf-rpi3-staging/mod_install/lib/modules/4.4.50-v7+/* ~/mnt/pi-root/lib/modules/4.4.50-v7+/.
sed -i '/^\/dev\/mmcblk0p1/s/^/#/' ~/mnt/pi-root/etc/fstab

umount ~/mnt/pi-boot
umount ~/mnt/pi-root
