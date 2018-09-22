---
layout: page
tocref: uber eXtensible Micro-Hypervisor Framework Documentation &gt; rpi3-cortex_a53-armv8_32  
title: Installing
---

Refer to the [build process]({% link docs/rpi3-cortex_a53-armv8_32/build.md %})
to build the required binaries for installation. Then proceed with the 
following instructions to deploy uberXMHF on the SD card:

1. `mkdir -p ~/mnt/pi-boot`

1. `mkdir -p ~/mnt/pi-root`

1. `sudo mount /dev/mmcblk0p1 ~/mnt/pi-boot`

1. `sudo mount /dev/mmcblk0p2 ~/mnt/pi-root`

1. `sudo cp ~/uxmhf-rpi3-staging/uhcalltest ~/mnt/pi-root/home/pi/.`

1. `sudo cp ~/uxmhf-rpi3-staging/uhcallkmod.ko ~/mnt/pi-root/home/pi/.`

1. `sudo cp ~/uxmhf-rpi3-staging/uxmhf-rpi3.img ~/mnt/pi-boot/.`

1. `sudo cp ~/uxmhf-rpi3-staging/config.txt ~/mnt/pi-boot/.`

1. Append `loglevel=8 memblock=debug dwc_otg.fiq_enable=0 dwc_otg.fiq_fsm_enable=0` to `~/mnt/pi-boot/cmdline.txt`

1. `sudo cp ~/uxmhf-rpi3-staging/boot/* ~/mnt/pi-boot/.`

1. `sudo mkdir -p ~/mnt/pi-boot/overlays`

1. `sudo cp -R ~/uxmhf-rpi3-staging/overlays/* ~/mnt/pi-boot/overlays/.`

1. `sudo cp ~/uxmhf-rpi3-staging/kernel7.img ~/mnt/pi-boot/.`

1. `sudo mkdir -p ~/mnt/pi-root/lib/firmware`

1. `sudo cp -R ~/uxmhf-rpi3-staging/mod_install/lib/firmware/* ~/mnt/pi-root/lib/firmware/.`

1. `sudo mkdir -p ~/mnt/pi-root/lib/modules/4.4.50-v7+`

1. `sudo cp -R ~/uxmhf-rpi3-staging/mod_install/lib/modules/4.4.50-v7+/* ~/mnt/pi-root/lib/modules/4.4.50-v7+/.`

1. Edit `~/mnt/pi-root/etc/fstab` and comment out line beginning with `/dev/mmcblk0p1` which is mounted to boot


