FROM ubuntu:16.04

RUN apt-get update && \
    apt-get install -yqq build-essential autoconf autotools-dev git bc

RUN git clone https://github.com/raspberrypi/tools

ENV PATH=/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/:${PATH}

RUN git clone https://github.com/raspberrypi/linux.git --depth 1 --branch rpi-4.4.y --single-branch && \
    cd linux && export KERNEL=kernel7 && \
    make ARCH=arm CROSS_COMPILE=/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/arm-linux-gnueabihf- bcm2709_defconfig && \
    make -j 4 ARCH=arm CROSS_COMPILE=/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/arm-linux-gnueabihf- zImage modules dtbs && \
    mkdir -p /uxmhf-rpi3-staging/mod_install && \
    make -j 4 ARCH=arm CROSS_COMPILE=/tools/arm-bcm2708/arm-rpi-4.9.3-linux-gnueabihf/bin/arm-linux-gnueabihf- INSTALL_MOD_PATH=/uxmhf-rpi3-staging/mod_install/ modules_install && \
    ./scripts/mkknlimg arch/arm/boot/zImage /uxmhf-rpi3-staging/$KERNEL.img && \
    mkdir -p /uxmhf-rpi3-staging/overlays && \
    cp ./arch/arm/boot/dts/overlays/*.dtb* /uxmhf-rpi3-staging/overlays/. && \
    cp ./arch/arm/boot/dts/overlays/README /uxmhf-rpi3-staging/overlays/. && \
    mkdir -p /uxmhf-rpi3-staging/boot && \
    cp ./arch/arm/boot/dts/*.dtb /uxmhf-rpi3-staging/boot/. && cd ..

RUN git clone https://github.com/hypcode/uberxmhf.git && \
    cd uberxmhf/uxmhf-rpi3 && ./bsconfigure.sh && ./configure && \
    make clean && make OSKRNLIMG=/uxmhf-rpi3-staging/kernel7.img && \
    cp uxmhf-rpi3.img /uxmhf-rpi3-staging/. && \
    cp rpi3-config.txt /uxmhf-rpi3-staging/config.txt

RUN cd /uberxmhf/uxmhf-rpi3/rgapps/linux/rgapp-uhcallkmod && \
    ./build.sh /linux /tools/arm-bcm2708/gcc-linaro-arm-linux-gnueabihf-raspbian-x64/bin/ && \
    cp ./uhcallkmod.ko /uxmhf-rpi3-staging/.

RUN cd /uberxmhf/uxmhf-rpi3/rgapps/linux/ && make -w all && cd rgapp-uhcalltest && \
    make -w all && cp ./uhcalltest /uxmhf-rpi3-staging/.

COPY transfer.sh /

RUN /bin/bash
