# Quick Start

Optionally, choose a `PREFIX` where you will install various utilities,
libraries, and headers. The default `PREFIX` is `/usr/local`.

Optionally, choose a host-name to use for PAL code. The default `HOST`
is `i586-tsvc`.

Optionally, choose a `SYSROOT`, where libraries to be linked against PAL
code will be installed. The default is `$(PREFIX)/$(HOST)`

Ensure that the trustvisor headers are installed for both the host and
the cross-development `SYSROOT`.

    :::sh
    cd $(TRUSTVISOR_CODE_DIR)
    ./configure --prefix=$(SYSROOT)/usr
    make install-dev
    ./configure --prefix=$(PREFIX)
    make install-dev

Run `make` in the same directory as this README. If you would like to
override the default paths, specify your overrides as parameters to `make`:

    :::sh
    make PREFIX=$(PREFIX) HOST=$(HOST) SYSROOT=$(SYSROOT)

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

# Overview

This is the Trusted-Execution-Environment Software-Development-Kit
(tee-sdk). It comprises tools and documentation for developing
_services_ that run in a trusted environments, and _clients_ that
communicate with those services. Initially, this means writing PALs
that run under TrustVisor, and applications that use PALs. However,
the APIs provided here are intended to provide sufficient abstraction
such that additional back-ends can be implemented, allowing services
and applications to be ported to use alternative trusted environments
with little or no modification.

# Terminology

Service
  ~ A piece of code running in a trusted execution environment
    provided by a _device_. (e.g., a PAL)
Client
  ~ An application that communicates with one or more _services_.
Device
  ~ A module providing a trusted execution environment (e.g., TrustVisor)

# Files

  * [tz](tz) TrustZone API. This library is to be used by _clients_
    to communicate with _services_. This library supports multiple
    _device_ back-ends, abstracting them in such a way that most _client_
    code can be oblivious to which back-end is in use.
  * [toolchain](toolchain) A cross-compiling toolchain for compiling
    and linking PALs. Implemented as wrappers around gcc.
  * [ports](ports) Support libraries for _services_. These have been
    ported to run in a trusted environment provided by some _device_.
    i.e., they do not make system calls, and all dependencies should
    be satisfied by other ports, svcapi, or other libraries provided
    as part of this package.
  * [examples](examples) Examples and tests.
  
# Build and installation

You will need to build and install in [tz](tz):

    :::sh
    cd tz
    autoreconf -i # Generates configure script
    ./configure
    make
    sudo make install

By default, everything will install into `/usr/local`. You can of course
change this by passing `--prefix=$tzinstallprefix` to the configure
script.

# Compiling applications

The previous step installs several libraries. There is a front-end
library for applications (tee-sdk-app), a front-end library for
services (tee-sdk-svc), and for each device there are application and
service back-end libraries (tee-sdk-app-devname and
tee-sdk-svc-devname). 

We use [pkgconfig][1] to simplify management of these libraries.  The
compile time flags needed to link against a package can be obtained
using `pkg-config --cflags packagename`. The linking flags can be
obtained using `pkg-config --libs --static packagename`. Note that we
only support static linking for now. If you installed [tz](tz) to a
non-standard location `$tzinstallprefix`, you may need to set
`PKG_CONFIG_LIBDIR` to include `$tzinstallprefix/lib/pkgconfig`.

[1]: http://pkg-config.freedesktop.org/wiki/

An application using the tee-sdk to communicate with a service running
in a trusted environment must link against at least one application
back-end. It is also permissable to link against multiple back-ends; a
single application can communicate with services running on multiple
devices. 

# Compiling services (PALs)

You must compile and link using exactly one service back-end
package. At the time of this writing, there is only one anyways:
`tee-sdk-svc-tv`. pkgconfig will automatically pull in the service
front-end `tee-sdk-svc` as a dependency. Using the compile and link
flags from those packages is important not only to link against the
corresponding libraries; they also reference compiler options to
eliminate code-constructs that are unsupported inside services, and
linker options to ensure the necessary layout in the final binary.

Services to be run under TrustVisor need to be compiled somewhat
specially. A PAL is linked together into the same binary with the
application that runs it. At run-time, the application registers the
PAL with TrustVisor. Using the raw TrustVisor interfaces for PAL
management, you'd need to keep track of which address ranges belong to
PAL code, data, etc., and make sure those sections are page-aligned.
Things can get tricky if you want some code to be accessible to both
the PAL code and the application code, and trickier still if you want
to use different implementations for the same function in PAL and
application code (such as linking the PAL against a version of libc
that doesn't make system calls while linking the regular code with the
standard version of libc).

The TEE-SDK has some tools to take care of these details for you. The
basic approach is use _partial linking_ to link all PAL code into a
single object file (.o), rewrite all symbols except for the PAL
entry-point in that object file to be private, and then use a linker
script to link this object file with the regular application while
mapping the PAL's code and data to special page-aligned sections. The
TrustVisor back-end provides simplified functions for registering a
PAL that has been built and linked this way.

The TEE-SDK includes `pkg-config` files that specify the necessary
compilation and link flags, and Makefile snippets that can be included
in your own Makefiles to automate most of the process. Pointing your
makefile at those makefile snippets and\or `pkg-config` files (rather
than copying and modifying a monolithic Makefile with these things
hard-coded) will help keep your pal up to date as the build process
evolves. See [examples/newlib/Makefile](examples/newlib/Makefile) for
a good starting point of a Makefile that dynamically incorporates the
TEE-SDK-provided Makefile snippets and pkg-config files.

# Compiling and running the test example

After installation in [tz](tz), you should be able to compile and run
the test example in [examples/test](examples/test). Remember to set
the `PKG_CONFIG_LIBDIR` environment variable if you installed to a
non-system directory.

# Loading and unloading services

Services are loaded and unloaded through the TrustZone service manager:

    :::c
    tz_return_t tzRet;
    tz_device_t tzDevice;
    tz_session_t tzManagerSession;
    tz_uuid_t tzSvcId;

    /* open isolated execution environment device */
    /* Use NULL for default device, or 'tv' to specify trustvisor */
    tzRet = TZDeviceOpen(NULL, NULL, &tzDevice);
    assert(tzRet == TZ_SUCCESS);

    /* prepare service descriptor */
    /* this is currently device-specific (i.e., trustvisor-specific).
       eventually it'd be good to provide a common abstraction here. */
    scode_sections_info_init(&scode_info,
                             &__scode_start, scode_ptr_diff(&__scode_end, &__scode_start),
                             NULL, 0,
                             PAGE_SIZE, PAGE_SIZE);

    /* open session with device manager */
    tzRet = TZManagerOpen(&tzDevice, NULL, &tzManagerSession);
    assert(tzRet == TZ_SUCCESS);

    /* download */
    tzRet = TZManagerDownloadService(&tzManagerSession,
                                     &pal,
                                     sizeof(pal),
                                     &tzSvcId);
    assert(tzRet == TZ_SUCCESS);

    /* do useful work with the service */
  
    /* unload the service. */
    /* This is currently CRITICAL when using TrustVisor. Exiting the
       application without unloading the service will lead to system
       instability. */
    tzRet = TZManagerRemoveService(&tzManagerSession,
                                   &tzSvcId);
    assert(tzRet == TZ_SUCCESS);

    /* close session */
    tzRet = TZManagerClose(&tzManagerSession);
    assert(tzRet == TZ_SUCCESS);

The TrustVisor back-end provides some convenience functions for an
application to load an unload a single PAL:

    :::c
    tz_device_t tzDevice;
    tz_session_t tzPalSession;
    tz_uuid_t tzSvcId;
    tz_return_t rv;
    int rv=0;
  
    /* configurable options */
    pal_fn_t *pal_fn = &pal_entry_point;
    size_t param_size = PAGE_SIZE;
    size_t stack_size = PAGE_SIZE;

    /* register the pal */
    rv = tv_tz_init(&tzDevice,
                    &tzPalSession,
                    &tzSvcId,
                    pal_entry_point,
                    param_size,
                    stack_size);
    assert(rv == TZ_SUCCESS);

    /* do useful work with the pal */
    /* .... */

    /* register the pal */
    rv = tv_tz_teardown(&tzDevice,
                        &tzPalSession,
                        &tzSvcId);
    assert(rv == TZ_SUCCESS);

# Calling services

Services are called through the TrustZone API. You must open a session
with a currently-loaded service. A session can be used for multiple
invocations of a service. See the
[TrustZone API specification](tz/TrustZone_API_3.0_Specification.pdf)
for details.

# Developing a service

Unfortunately this area still needs a lot of work. It is currently
very trustvisor-specific and fragile. Everything here is likely to
change significantly.

## Memory Layout

While eventually services will be compiled as standalone binaries,
currently they are compiled together with the application that calls
them. When loading the service, memory pages that contain service code
and data are registered with trustvisor to be measured and protected.
This means that service code and data must be on separate memory
pages from application code and data, and that you must be able to identify
the relevant memory ranges. This is most easily done by putting service
code in separate object files or in separate sections, e.g.


A linker script must then be used to ensure page-alignment, and to
identify the beginning and end of the relevant sections. See
[examples/test/inject.ld] for an example of such a linker script.

## Service entry point

The service entry point should have the following prototype:

    :::c
    void pal_entry(uint32_t uiCommand,
                   tzi_encode_buffer_t *psInBuf,
                   tzi_encode_buffer_t *psOutBuf,
                   tz_return_t *puiRv)

 * `uiCommand` will contain command specified in the call to
   `TZOperationPrepareInvoke`
 * `psInBuf` will contain the parameters marshalled by `TZEncode*`. 
   Use the API in [tz/include/marshal.h] to decode this buffer.
 * `psOutBuf` is an output buffer for marshalled data. Use the
   API in [tz/include/marshal.h] to encode this buffer.
 * `puiRv` is a status code to be returned. Success should be indicated
   by setting this to `TZ_SUCCESS`.

# Roadmap

## Clean API for developing services

We need to define a common clean interface for the runtime that
a device provides to a service. This is currently defined by
svcapi.h.

## Support for standalone service binaries

For the moment, services and the applications that interact with them
are compiled into the same binary. Support for standalone service
binaries will help decouple these. In the first iteration, these will
probably have to be statically compiled position-independent binaries.

The current API for loading services is trustvisor-specific, and
requires that the service (PAL) and the application that invokes it
are compiled into the same binary. Soon we'll standardize a standalone
binary format for services, so that they may be compiled separately
from the applications that use them. Ideally they will also be at least
source-compatible with alternative devices; perhaps even binary-compatible.

## User-space device

It should be fairly straightforward to create a device that runs a
service in user-space, while emulating both the functionality and
limitations of a trusted environment. This would help a lot with
debugging. A clean way to simulate this would be to fork a new process
to run the service code, passing data through shared mmap regions.

