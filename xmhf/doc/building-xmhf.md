Development Environment
=======================

[XMHF](..) and hypapps (e.g., [TrustVisor](../../hypapps/trustvisor), 
[Lockdown](../../hypapps/lockdown)) get built in a Linux environment with 
a recent version of gcc. XMHF has been verified to build on Ubuntu 
10, 11, and 12 series, both 32 and 64 bit.


Build tools
===========

A (partial) list of packages to install:

    aptitude install pbuilder texinfo ruby build-essential autoconf libtool

On 64-bit platforms, you will also need to install 32-bit
libraries. On Ubuntu 12:

    aptitude install gcc-multilib


High-level Build Summary
========================

One "drives" the build from the root directory of XMHF package.  

The interesting high-level build commands include:

    ./autogen.sh           # creates ./configure
    ./configure            # creates Makefile from Makefile.in
    make                   # builds the selected hypapp and the XMHF core
    make install           # installs binaries
    make install-dev       # (hypapp specific) installs dev headers and libs
    make test              # (hypapp specific) runs various automated tests
    make clean             # cleanup

The functioning of `make install-dev` and `make test` are
hypapp-specific. For example, in TrustVisor, the primary prerequisite
for tee-sdk and PAL development is having successfully run `make
install-dev`.


How do I build an XMHF hypapp?
==============================

The method for building different hypapps (e.g., TrustVisor,
Lockdown) is by specifying which hypapp to build using `./configure`.
The following describes the sequence of steps for building a XMHF
hypapp using the helloworld hypapp as a running example.

Checkout the XMHF project source tree.

    cd $WORK
    git clone git://git.code.sf.net/p/xmhf/xmhf xmhf

Change working directory to the root directory.

    cd $WORK/xmhf

Generate the `./configure` script.

    ./autogen.sh

Configure the XMHF hypapp.

    ./configure --with-approot=hypapps/helloworld
   
Generate and install the binaries:

    make
    make install
    make install-dev  # optional (hypapp-specific)
    make test         # optional (hypapp-specific)

Note that `make install` is only useful if the development system and 
the target system (on which XMHF is installed) are the same. If not, 
you will need to manually copy the files `$WORK/xmhf/init-x86.bin` 
and `$WORK/xmhf/hypervisor-x86.bin.gz` to the `/boot` folder of the
target system (see [Installing XMHF](./installing-xmhf.md)).  


Build configuration options
===========================

* --with-approot=[HYPAPPPATH], specifies the hypapp source root; must be provided

* --with-target-platform=[PLATFORM], specifies the target platform for the build; 
optional, current options are: x86pc (x86 hardware virtualized platforms, default)

* --with-target-arch=[ARCH], specifies the target CPU architecture; 
optional, current options are: x86vmx (Intel, default), x86svm (AMD)

* --disable-drt, disables Dynamic Root-of-Trust (DRT); optional, useful for builds 
targeting platforms without support for DRT and/or TPM

* --disable-dmap, disables DMA protection; optional, useful for builds targeting 
platforms without DMA protection capabilities
