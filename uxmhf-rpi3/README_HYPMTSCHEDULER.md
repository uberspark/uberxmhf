# Quick start to using uberXMHF Raspberry PI 3

1.  Prepare raspberry pi sd-card image
	1. Download https://downloads.raspberrypi.org/raspbian_lite/images/raspbian_lite-2016-11-29/2016-11-25-raspbian-jessie-lite.zip
	1. Use [win32diskimager](https://sourceforge.net/projects/win32diskimager/) under Windows OS to burn contents of .zip
	1. Use ImageWriter tool under Ubuntu
	
1. Development system (VM, baremetal or Windows/WSL with Ubuntu 16.04.x) setup
	1. `sudo apt-get update`
	1. `sudo apt-get install build-essential autoconf autotools-dev`
	1. `sudo apt-get install git`
	1. `sudo apt-get install bc`
	
1. Install Raspberry PI development tools on development system
	1. `git clone https://github.com/raspberrypi/tools`
	1. Add `~/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/` to `PATH`

1. Install and build RPI kernel on development system
	1. `git clone https://github.com/raspberrypi/linux.git`
	1. `cd linux`
	1. `git checkout rpi-4.4.y`
	1. `export KERNEL=kernel7`
	1. `make ARCH=arm CROSS_COMPILE=~/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/arm-linux-gnueabihf- bcm2709_defconfig`
	1. `make -j 4 ARCH=arm CROSS_COMPILE=~/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/arm-linux-gnueabihf- zImage modules dtbs`
	1. `mkdir -p ~/uxmhf-rpi3-staging/mod_install`
	1. `make -j 4 ARCH=arm CROSS_COMPILE=~/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/arm-linux-gnueabihf- INSTALL_MOD_PATH=~/uxmhf-rpi3-staging/mod_install/ modules_install`
	1. `./scripts/mkknlimg arch/arm/boot/zImage ~/uxmhf-rpi3-staging/$KERNEL.img`
	1. `mkdir -p ~/uxmhf-rpi3-staging/overlays`
	1. `cp ./arch/arm/boot/dts/overlays/*.dtb* ~/uxmhf-rpi3-staging/overlays/.`
	1. `cp ./arch/arm/boot/dts/overlays/README ~/uxmhf-rpi3-staging/overlays/.`
	1. `mkdir -p ~/uxmhf-rpi3-staging/boot`
	1. `cp ./arch/arm/boot/dts/*.dtb ~/uxmhf-rpi3-staging/boot/.`

1. Obtain sd-card boot-partition extents
	1. `sudo fdisk -l /dev/mmcblk0`
	1. note down start sector of /dev/mmcblk0p0 in the output (`BP_START_SECTOR`)
	1. note down end sector of /dev/mmcblk0p0 in the output (`BP_END_SECTOR`)
	
1. Build uberXMHF Raspbery PI 3 on development system
	1. `cd uxmhf-rpi3`
	1. `./bsconfigure.sh`
	1. `./configure --with-boot-partition-start=BP_START_SECTOR --with-boot-partition-end=BP_END_SECTOR` 
	1. `make clean`
	1. `make OSKRNLIMG=~/uxmhf-rpi3-staging/kernel7.img`
	1. `cp uxmhf-rpi3.img ~/uxmhf-rpi3-staging/.`
	1. `cp rpi3-config.txt ~/uxmhf-rpi3-staging/config.txt`

1. Building `uhcallkmod` on development system
	1. `cd rgapps/linux/rgapp-uhcallkmod`
	1. `./build.sh ~/linux ~/tools/arm-bcm2708/gcc-linaro-arm-linux-gnueabihf-raspbian-x64/bin/`
	1. `cp ./uhcallkmod.ko ~/uxmhf-rpi3-staging/.`

1. Building `uhcalltest` on development system
	1. `cd rgapps/linux`
	1. `make -w all`
	1. `cd rgapp-uhcalltest`
	1. `make -w all`
	1. `cp ./uhcalltest ~/uxmhf-rpi3-staging/.`
	
1. Deploying on sd-card
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

1. Setup serial debugging
	1. Required: USB to TTL Serial Debug Cable for Raspberry Pi; available [here](https://www.adafruit.com/product/954?gclid=Cj0KCQjw_ODWBRCTARIsAE2_EvVn-6n_HsU-McCFk-ffkiPooqiDkVjVaZtq39GAIyy5s8Ep5yb6K9QaAtKQEALw_wcB)
	1. Connect Pin 6 on PI to GND of serial cable; Pin 8 to RX and Pin 10 to TX
	1. Edit `~/mnt/pi-boot/config.txt` and add the following lines: <br>
		`enable_uart=1` <br>
		`init_uart_baud=115200` <br>
		`force_turbo=0`

1. Boot up and test
	1. `umount ~/mnt/pi-boot`
	1. `umount ~/mnt/pi-root`
	1. Insert sd-card into the Raspberry PI 3
	1. On a seperate terminal in the development system execute: `sudo screen /dev/ttyUSB0 115200 8N1`
	1. Power on the Raspberry PI 3
	1. ... and you should see uberXMHF booting up with debug output and the guest starting soon thereafter


