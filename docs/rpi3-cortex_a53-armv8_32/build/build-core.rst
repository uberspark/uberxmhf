.. include:: /macros.rst


Build Micro-Hypervisor Core Framework
=====================================

#. 
   Prepare raspberry pi sd-card image


   #. Download https://downloads.raspberrypi.org/raspbian_lite/images/raspbian_lite-2016-11-29/2016-11-25-raspbian-jessie-lite.zip
   #. Use `win32diskimager <https://sourceforge.net/projects/win32diskimager/>`_ under Windows OS to burn contents of .zip
   #. Use ImageWriter tool under Ubuntu

#. 
   Boot into raspbian using the sd-card on the pi and resize the root filesystem to
   fit the entire sd card. Use the following commands once logged in:


   #. ``sudo raspi-config``
   #. (optional) run the bottom option ``update`` to make sure you have latest version of
      the configuration software
   #. run the second option ``expand_rootfs``
   #. click ``finish``
   #. select ``YES`` when asked for a reboot

#. 
   Development system (VM, baremetal or Windows/WSL with Ubuntu 16.04.x) setup


   #. ``sudo apt-get update``
   #. ``sudo apt-get install build-essential autoconf autotools-dev``
   #. ``sudo apt-get install git``
   #. ``sudo apt-get install bc``

#. 
   Install Raspberry PI development tools on development system


   #. ``git clone https://github.com/raspberrypi/tools``
   #. Add ``~/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/`` to ``PATH``

#. 
   Install and build RPI kernel on development system


   #. ``git clone https://github.com/raspberrypi/linux.git``
   #. ``cd linux``
   #. ``git checkout rpi-4.4.y``
   #. ``export KERNEL=kernel7``
   #. ``make ARCH=arm CROSS_COMPILE=~/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/arm-linux-gnueabihf- bcm2709_defconfig``
   #. ``make -j 4 ARCH=arm CROSS_COMPILE=~/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/arm-linux-gnueabihf- zImage modules dtbs``
   #. ``mkdir -p ~/uxmhf-rpi3-staging/mod_install``
   #. ``make -j 4 ARCH=arm CROSS_COMPILE=~/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/arm-linux-gnueabihf- INSTALL_MOD_PATH=~/uxmhf-rpi3-staging/mod_install/ modules_install``
   #. ``./scripts/mkknlimg arch/arm/boot/zImage ~/uxmhf-rpi3-staging/$KERNEL.img``
   #. ``mkdir -p ~/uxmhf-rpi3-staging/overlays``
   #. ``cp ./arch/arm/boot/dts/overlays/*.dtb* ~/uxmhf-rpi3-staging/overlays/.``
   #. ``cp ./arch/arm/boot/dts/overlays/README ~/uxmhf-rpi3-staging/overlays/.``
   #. ``mkdir -p ~/uxmhf-rpi3-staging/boot``
   #. ``cp ./arch/arm/boot/dts/*.dtb ~/uxmhf-rpi3-staging/boot/.``

#. 
   Build uberXMHF Raspbery PI 3 on development system


   #. ``cd uxmhf-rpi3/uobjcoll``
   #. ``uberspark build -v``
   #. ``cd install && ./install.sh ~/uxmhf-rpi3-staging/kernel7.img`` 
   #. ``cp install/uxmhf-rpi3.img ~/uxmhf-rpi3-staging/.``
   #. ``cp install/rpi3-config.txt ~/uxmhf-rpi3-staging/config.txt``

   .. note::   the option ``-v`` above, is optional and enables verbose debugging information
               for the |uspark| command line tool. 


#. 
   Note: you can enable optional core micro-hypervisor features by enabling
   the following definitions within the ``uberspark.uobjcoll.configdefs`` JSON
   node within ``uxmhf-rpi3/uobjcoll/uberspark.json`` as needed:


   #. set ``dmaprot`` to ``@@TRUE@@`` to enable DMA protection capabilities
   #. set ``secboot`` to ``@@TRUE@@`` with ``uxmhf_boot_partition_start_bp_start_sector`` 
      and ``uxmhf_boot_partition_end_bp_end_sector`` to enable 
      secure boot capabilities. The start and end sector values are
      the values of the starting and ending sectors of the 
      boot partition (\ ``/dev/mmcblk0p0``\ ) as obtained from the output of the 
      following command: 
      ``sudo fdisk -l /dev/mmcblk0``. Replace ``/dev/mmcblk0`` with the sdcard 
      device on the development system.
   #. set ``intprot`` to ``@@TRUE@@`` to enable interrupt protection capabilities
   #. set ``fiqreflection`` to ``@@TRUE@@`` to enable guest FIQ interrupts to be 
      handled within micro-hypervisor
   #. set ``debug_uart`` to ``@@TRUE@@`` to enable debug output via UART; you must 
      additionally either specify,
      Mini UART (via ``enable_uart_mini``) or full (PL011) 
      UART (via ``enable_uart_pl011``).
      Also, if using PL011 UART, you can use 
      ``enable_uart_pl011_ctsrts`` to enable UART hardware flow control. 




