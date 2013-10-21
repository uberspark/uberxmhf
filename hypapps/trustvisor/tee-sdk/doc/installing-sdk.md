Installing TrustVisor Headers
=============================

On a machine where you are planning to develop PALs, you will also
need to install the [TrustVisor](../../) development headers. The
[tee-sdk](../) currently expects those headers to be
installed in two places.

*First*, install the headers in a 'normal' system location. This can be
installed by `make install-dev`, when you build
[TrustVisor](../../doc/building-trustvisor.md). 
If you directly install TrustVisor binary on your platform without building 
it, please download and uncompress the XMHF package, go to the root directory 
and run the following commands:

	./autogen.sh
	./configure --with-approot=hypapps/trustvisor
    make install-dev

*Second*, you will then need to reconfigure to point to the Trustvisor PAL
cross-compilation environment and install the headers again:

    ./configure --with-approot=hypapps/trustvisor --prefix=$(SYSROOT)/usr
    make install-dev

Note: $(SYSROOT) depends on your configuration of building TEE-SDK,
see below for more details. The default $(SYSROOT) is `/usr/local/i586-tsvc`

Downloading and Patching Third Party Libraries
==============================================

Before installing TEE-SDK, you need to download a few third party
libraries (e.g., newlib, openssl), and apply patches to them so 
that they could be used for PAL development.

For newlib library, we use newlib-1.19.0 version. 
Download the `newlib-1.19.0.tar.gz` from http://sourceforge.net/projects/devkitpro/files/sources/newlib/, 
untar it to ../ports/newlib/ directory, then execute the following commands:

	cd ../ports/newlib/newlib-1.19.0
	patch -p1 < ../newlib-tee-sdk-131021.patch

For openssl library, we use openssl-1.0.0d version.
Download the `openssl-1.0.0d.tar.gz` from http://www.openssl.org/source/,
untar it to ../ports/openssl/ directory, then execute the following commands:

	cd ../ports/openssl/openssl-1.0.0d
	patch -p1 < ../openssl-tee-sdk-131021.patch
Note that you would have prompt as follows:
	Reversed (or previously applied) patch detected!  Assume -R? [n] 
	Apply anyway? [n]
This is caused by trying to patch the symbolic link file in
include/openssl/opensslconf.h, which is unnecessary. 
Just press Enter twice to skip them, and ignore the .rej file created.


Building and Installing TEE-SDK
===============================

After installing TrustVisor headers, downloading and patching third party
libraries, go to TEE-SDK directory and run
`make` to build and install TEE-SDK.

If you would like to override the default paths, specify your overrides 
as parameters to `make`:

    make PREFIX=$(PREFIX) HOST=$(HOST) SYSROOT=$(SYSROOT)

$(PREFIX) specifies where you will install various utilities,
libraries, and headers. The default $(PREFIX) is `/usr/local`.

$(HOST) is the host-name to use for PAL code. The default $(HOST)
is `i586-tsvc`.

$(SYSROOT) points to the path where libraries to be linked against PAL
code will be installed. The default $(SYSROOT) is `$(PREFIX)/$(HOST)`

Of course, you may install each tee-sdk component individually, 
either by specifying a target to `make`, or by manually performing the
steps in the corresponding make recipe. At the time of this writing,
the components installed by `make` are:

* toolchain : these are wrappers to utilities such as gcc, with names
  like `i586-tsvc-gcc`. They mostly serve to override the system paths
  with paths in $(SYSROOT).

* tz : This implements the TrustZone API for managing and
  communicating with services (pals) running the trusted execution
  environment (trustvisor).

* newlib : this is an implementation of libc targeted for
  PALs. Functions that do not involve IO should work as expected. IO
  functions currently fail gracefully. The toolchain `i586-tsvc-gcc`
  will link against this library by default, unless `-nostdlib` is used.

* openssl : This is the well-known openssl library, ported for use
  with pals. It is not installed by default, but can be installed with
  `make openssl`
