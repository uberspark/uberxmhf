Development Environment
=======================

[XMHF](..) and its Apps (e.g., [TrustVisor](../../trustvisor)) get
built in a Linux environment with a recent version of gcc. [XMHF](..)
has been verified to build on Ubuntu 10, 11, and 12 series, both 32
and 64 bit.

Build tools
===========

A (partial) list of packages to install:

    aptitude install pbuilder texinfo ruby build-essential autoconf libtool

On 64-bit platforms, you will also need to install 32-bit
libraries. On Ubuntu 12:

    aptitude install gcc-multilib

High-level Build Summary
========================

One "drives" the build from `xmhf/xmhf`.  

The interesting high-level build commands include:

    cd xmhf/xmhf
    ./autogen.sh           # creates ./configure
    ./configure            # creates Makefile from Makefile.in
    make                   # Builds the selected hypapp and the XMHF core
    make install           # Installs both binaries and dev headers and libs
    make install-dev       # Installs just dev headers and libs
    make test              # Runs various automated tests
    make clean             # Deletes all object files
    make init-late         # Explicitly builds the Linux kernel module for
                           # a dynamic late launch

The functioning of `make install-dev` and `make test` are
hypapp-specific. For example, in TrustVisor, the primary prerequisite
for tee-sdk and PAL development is having successfully run `make
install-dev` in `xmhf/xmhf`.

How do I build an XMHF hypapp?
==============================

The preferred method for building different hypapps (e.g., TrustVisor,
Lockdown) is by specifying which hypapp to build using `./configure`.
The following describes the sequence of steps for building a XMHF
hypapp using the helloworld hypapp as a running example.

Checkout the XMHF project source tree.

    cd $WORK
    git clone git://git.code.sf.net/p/xmhf/xmhf xmhf

Change working directory to the XMHF source tree root.

    cd $WORK/xmhf/xmhf

Generate the `./configure` script.

    ./autogen.sh

Configure the XMHF hypapp.

    ./configure --with-approot=src/example-hypapps/helloworld --with-apparchive=xmhfapp-helloworld.a
   
Generate and install the binaries (note: default install path is specified with the `--prefix=` flag to `configure`).

    make
    make install
    make install-dev  # optional (hypapp-specific)
    make test         # optional (hypapp-specific)

