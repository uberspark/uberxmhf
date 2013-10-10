Installing TrustVisor Headers
=============================

On a machine where you are planning to develop PALs, you will also
need to install the [TrustVisor](../../) development headers. The
[tee-sdk](../) currently expects those headers to be
installed in two places.

*First*, install the headers in a 'normal' system location. This is
done when you build and install TrustVisor. If you install TrustVisor
binary on the machine without building it, please download and untar
XMHF package, go to the root directory and run the following commands:

	./autogen.sh
	./configure --with-approot=hypapps/trustvisor
    make install-dev

*Second*, you will then need to reconfigure to point to the PAL
cross-compilation environment (e.g., i586-tsvc by default), 
and install the headers again:

    ./configure --with-approot=/path/to/tv --prefix=$(SYSROOT)/usr
    make install-dev

Note: $(SYSROOT) depends on your configuration of building TEE-SDK,
see below for more details. The default $(SYSROOT) is /usr/local/i586-tsvc


Building and Installing TEE-SDK
===============================

After installing TrustVisor headers, go to TEE-SDK directory and run
`make` to build and install TEE-SDK.

If you would like to override the default paths, specify your overrides 
as parameters to `make`:

    make PREFIX=$(PREFIX) HOST=$(HOST) SYSROOT=$(SYSROOT)

Optionally, choose a `PREFIX` where you will install various utilities,
libraries, and headers. The default `PREFIX` is `/usr/local`.

Optionally, choose a host-name to use for PAL code. The default `HOST`
is `i586-tsvc`.

Optionally, choose a `SYSROOT`, where libraries to be linked against PAL
code will be installed. The default is `$(PREFIX)/$(HOST)`

Of course, you may install each component individually, if you prefer,
either by specifying a target to 'make', or by manually performing the
steps in the corresponding 'make' recipe. At the time of this writing,
the components installed by make are:

* toolchain : these are wrappers to utilities such as gcc, with names
  like `i586-tsvc-gcc`. They mostly serve to override the system paths
  with paths in `$(SYSROOT)`.

* newlib : this is an implementation of libc targeted for
  PALs. Functions that don't involve IO should work as expected. IO
  functions currently fail gracefully. The toolchain `i586-tsvc-gcc`
  will link against this library by default, unless `-nostdlib` is used.

* tz : This implements the TrustZone API for managing and
  communicating with services (pals) running the trusted execution
  environment (trustvisor).

* openssl : This is the well-known openssl library, ported for use
  with pals. It is not installed by default, but can be installed with
  `make openssl`
