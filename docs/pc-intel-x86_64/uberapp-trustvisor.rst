.. include:: /macros.rst


|uberapp| - TrustVisor
======================

Introduction
------------

TrustVisor is a special-purpose hypervisor that provides measured, 
isolated execution environments for security-sensitive
code modules (Pieces of Application Logic - PALs) 
without trusting the OS or the application that invokes the code modules.

The isolated execution environment protects the code
integrity, execution integrity, as well as data integrity and secrecy
for PALs. TrustVisor produces evidence of
its initialization in the TPM's Platform Configuration Registers.
This evidence (in the form of a hash chain) can be used to generate a
TPM-based attestation that TrustVisor has loaded on a platform.
Further, TrustVisor implements a software-based, micro-TPM (uTPM) 
that can execute at higher speed on the platform's primary CPU than
hardware TPM. It also generates and manages its own identity keypair
that can be used to generate subsequent attestations to the isolation
and execution of individual PALs, leveraging the uTPM.

The implementation of TrustVisor contained herein leverages 
uberXMHF (pc-intel-x86_64).\ 
The original design and implementation of TrustVisor is described in:

*TrustVisor: Efficient TCB Reduction and Attestation*. Jonathan
M. McCune, Yanlin Li, Ning Qu, Zongwei Zhou, Anupam Datta, Virgil
Gligor, and Adrian Perrig. IEEE Symposium on Security and Privacy, May
2010.\ `(pdf) <http://www.ece.cmu.edu/~jmmccune/papers/MLQZDGP2010.pdf>`_

.. _building:

Building
--------

The TrustVisor build is primarily driven from the uberXMHF (pc-intel-x86_64) build process; 
see :doc:`Building uberXMHF (pc-intel-x86_64) </pc-intel-x86_64/build>`. When
running ``configure`` , you will need to set ``--with-approot=hypapps/trustvisor`` 
to point to the TrustVisor source code. To install trustvisor
development headers (for :ref:`teesdk` ), please 
use ``./configure --prefix=...`` to specify
the install path, and run ``make install-dev``.


Installing
----------

To *run* TrustVisor on a given machine, installation is similar to that
of any other hypapp. See :doc:`Installing uberXMHF (pc-intel-x86_64) </pc-intel-x86_64/installing>`.

Note that for certain platforms (e.g., HP EliteBook 2540p), if the TPM locality
are not properly configured, trustvisor crashes at startup when attempting to 
clear all TPM localities. An intrusive work-around is to restore 
the TPM to factory state via BIOS.

TrustVisor uses TPM NVRAM to securely store a master secret that is
used to derive its long-term encryption and MAC keys. During startup, if no NVRAM 
Index is found, Trustvisor will downgrade to a 'ephemeral'mode, generating a 
new MasterSecret. Please following the below guideline to define NVRAM spaces
for TrustVisor using TPM tools.

Disable the infineon driver
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Modern Ubuntu has a tendency to load the Infineon-specific v1.1b TPM
driver, when it should be using ``tpm_tis``.  Thus, we blacklist
``tpm_infineon``.  Don't forget to reboot after making this change.  It
is possible to manually remove this driver (\ ``modprobe -r
tpm_infineon``\ ) and ``modprobe tpm_tis``\ , if you know what you're
doing. In ``/etc/modprobe.d/blacklist.conf`` add

.. code-block:: c

   blacklist tpm_infineon


Shut down trousers, if it is running
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

See if trousers is running first, shut down if necessary.  It will
probably start up again after the next reboot.  You may wish to
uninstall it or disable it more permanently if you're not otherwise
using it.

.. code-block:: c

   /etc/init.d/trousers status
   /etc/init.d/trousers stop


Install jTpmTools
^^^^^^^^^^^^^^^^^

Our current testing has been with v0.6 but we will soon move to
v0.7. https://sourceforge.net/projects/trustedjava/files/jTPM%20Tools/

.. code-block:: c

   sudo dpkg -i jtpmtools_0.6.deb


Set the tpm device to be accessible by jtss
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: bash

   chown jtss:tss /dev/tpm0
   /etc/init.d/jtss start
   /etc/init.d/jtss status

   cat /var/log/jtss/tcs_daemon.log


Take ownership of the TPM
^^^^^^^^^^^^^^^^^^^^^^^^^

You will need to take ownership of the TPM, and set an owner
password. It is important not to lose the owner password that you
set. In TrustVisor's security model it is *not* security critical that
the owner password is not compromised, so feel free to use a well
known password or empty string if you are not using the TPM for other
purposes that might require a strong TPM owner password.

.. code-block:: bash

   jtt take_owner -e ASCII -o 'owner_password'


Define the NV spaces
^^^^^^^^^^^^^^^^^^^^

We actually define two nv spaces. One stores TrustVisor's master
secret. The other stores the root of a hash chain used for replay
protection (see [Memoir])

.. code-block:: bash

   jtt nv_definespace \
       --index 0x00015213 \
       --size 20 \
       -o 'owner_password' \
       -e ASCII \
       -p 11,12 \
       -w \
       --permission 0x00000000 \
       --writelocality 2 \
       --readlocality 2
   jtt nv_definespace \
       --index 0x00014e56 \
       --size 32 \
       -o 'owner_password' \
       -e ASCII \
       -p 11,12 \
       -w \
       --permission 0x00000000 \
       --writelocality 2 \
       --readlocality 2


Unload Linux TPM driver
^^^^^^^^^^^^^^^^^^^^^^^

Before running Trustvisor or PAL code that requires access to the NV
RAM, we need to ensure the Linux TPM device driver is indeed
removed. Hence, we want to stop all the drivers that rely on the Linux
TPM device driver.  This requirement will go away once issue 15 is
closed. https://sourceforge.net/p/xmhf/tickets/15/

.. code-block:: bash

   /etc/init.d/jtss stop
   modprobe -r tpm_tis

.. _teesdk:

Trusted Execution Environment (TEE) SDK
---------------------------------------

Overview
^^^^^^^^

The Trusted-Execution-Environment Software-Development-Kit
(tee-sdk) comprises tools and documentation for developing
*services* that run in a trusted environments, and *clients* that
communicate with those services, in Linux system. 
Initially, this means writing PALs that run under TrustVisor, 
and applications that use PALs. However,
the APIs provided here are intended to provide sufficient abstraction
such that additional back-ends can be implemented, allowing services
and applications to be ported to use alternative trusted environments
with little or no modification.

Terminology
^^^^^^^^^^^

Service
  ~ A piece of code running in a trusted execution environment
    provided by a *device*. (e.g., a PAL)
Client
  ~ An application that communicates with one or more *services*.
Device
  ~ A module providing a trusted execution environment (e.g., TrustVisor)

Files (relative to ``xmhf/hypapps/trustvisor/tee-sdk/``\ )
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


* tz/: TrustZone API. This library is to be used by *clients*
  to communicate with *services*. This library supports multiple
  *device* back-ends, abstracting them in such a way that most *client*
  code can be oblivious to which back-end is in use.
* toolchain/: A cross-compiling toolchain for compiling
  and linking PALs. Implemented as wrappers around gcc.
* ports/: Support libraries for *services*. These have been
  ported to run in a trusted environment provided by some *device*.
  i.e., they do not make system calls, and all dependencies should
  be satisfied by other ports, svcapi, or other libraries provided
  as part of this package.
* examples/: Examples and tests.


Installing TEE-SDK
------------------

Installing TrustVisor Headers
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

On a machine where you are planning to develop PALs, you will also
need to install the TrustVisor development headers. The
tee-sdk currently expects those headers to be
installed in two places.

*First*\ , install the headers in a 'normal' system location. This can be
installed by ``make install-dev``\ , when you build
:ref:`building`. 
If you directly install TrustVisor binary on your platform without building 
it, please download and uncompress the uberXMHF package, go to the ``xmhf`` 
directory 
and run the following commands:

.. code-block:: bash

   ./autogen.sh
   ./configure --with-approot=hypapps/trustvisor
   make install-dev


*Second*\ , you will then need to reconfigure to point to the Trustvisor PAL
cross-compilation environment and install the headers again:

.. code-block:: bash

   ./configure --with-approot=hypapps/trustvisor --prefix=$(SYSROOT)/usr
   make install-dev


Note: $(SYSROOT) depends on your configuration of building TEE-SDK,
see below for more details. The default $(SYSROOT) is ``/usr/local/i586-tsvc``

Downloading and Patching Third Party Libraries
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Before installing TEE-SDK, you need to download a few third party
libraries (e.g., newlib, openssl), and apply patches to them so 
that they could be used for PAL development.

For newlib library, we use newlib-1.19.0 version. 
Download the ``newlib-1.19.0.tar.gz`` from ftp://sourceware.org/pub/newlib/index.html, 
untar it to ../ports/newlib/ directory, then execute the following commands:

.. code-block:: bash

   cd ../ports/newlib/newlib-1.19.0
   patch -p1 < ../newlib-tee-sdk-131021.patch


For openssl library, we use openssl-1.0.0d version.
Download the ``openssl-1.0.0d.tar.gz`` from http://www.openssl.org/source/,
untar it to ../ports/openssl/ directory, then execute the following commands:

.. code-block:: bash

   cd ../ports/openssl/openssl-1.0.0d
   patch -p1 < ../openssl-tee-sdk-131021.patch


Note that you would have prompts as follows:

.. code-block:: bash

   Reversed (or previously applied) patch detected!  Assume -R? [n] 
   Apply anyway? [n]


This is caused by trying to patch the symbolic link file in
include/openssl/opensslconf.h, which is unnecessary. 
Just press Enter twice to skip them, and ignore the .rej file created.

Building and Installing TEE-SDK
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

After installing TrustVisor headers, downloading and patching third party
libraries, go to TEE-SDK directory and run
``make`` to build and install TEE-SDK.

If you would like to override the default paths, specify your overrides 
as parameters to ``make``\ :

.. code-block:: bash

   make PREFIX=$(PREFIX) HOST=$(HOST) SYSROOT=$(SYSROOT)


$(PREFIX) specifies where you will install various utilities,
libraries, and headers. The default $(PREFIX) is ``/usr/local``.

$(HOST) is the host-name to use for PAL code. The default $(HOST)
is ``i586-tsvc``.

$(SYSROOT) points to the path where libraries to be linked against PAL
code will be installed. The default $(SYSROOT) is ``$(PREFIX)/$(HOST)``

Of course, you may install each tee-sdk component individually, 
either by specifying a target to ``make``\ , or by manually performing the
steps in the corresponding make recipe. At the time of this writing,
the components installed by ``make`` are:


* 
  toolchain : these are wrappers to utilities such as gcc, with names
  like ``i586-tsvc-gcc``. They mostly serve to override the system paths
  with paths in $(SYSROOT).

* 
  tz : This implements the TrustZone API for managing and
  communicating with services (pals) running the trusted execution
  environment (trustvisor).

* 
  newlib : this is an implementation of libc targeted for
  PALs. Functions that do not involve IO should work as expected. IO
  functions currently fail gracefully. The toolchain ``i586-tsvc-gcc``
  will link against this library by default, unless ``-nostdlib`` is used.

* 
  openssl : This is the well-known openssl library, ported for use
  with pals. It is not installed by default, but can be installed with
  ``make openssl``


Using TEE-SDK
-------------

Compiling applications
^^^^^^^^^^^^^^^^^^^^^^

The TEE-SDK installs several libraries to the development machine. 
There is a front-end library for applications (tee-sdk-app), a 
front-end library for services (tee-sdk-svc), and for each device 
there are application and service back-end libraries 
(tee-sdk-app-devname and tee-sdk-svc-devname). 

We use `pkgconfig <http://pkg-config.freedesktop.org/wiki/>`_ to simplify management of these libraries.  The
compile time flags needed to link against a package can be obtained
using ``pkg-config --cflags packagename``. The linking flags can be
obtained using ``pkg-config --libs --static packagename``. Note that we
only support static linking for now. If you installed ``tz`` to a
non-standard location ``$tzinstallprefix``\ , you may need to set
``PKG_CONFIG_LIBDIR`` to include ``$tzinstallprefix/lib/pkgconfig``.

An application using the tee-sdk to communicate with a service running
in a trusted environment must link against at least one application
back-end. It is also permissable to link against multiple back-ends; a
single application can communicate with services running on multiple
devices. 

Compiling services (PALs)
^^^^^^^^^^^^^^^^^^^^^^^^^

You must compile and link using exactly one service back-end
package. At the time of this writing, there is only one anyways:
``tee-sdk-svc-tv``. pkgconfig will automatically pull in the service
front-end ``tee-sdk-svc`` as a dependency. Using the compile and link
flags from those packages is important not only to link against the
corresponding libraries; they also reference compiler options to
eliminate code-constructs that are unsupported inside services, and
linker options to ensure the necessary layout in the final binary.

Services to be run under TrustVisor need to be compiled somewhat
specially. A PAL is linked together into the same binary with the
application that runs it. At run-time, the application registers the
PAL with TrustVisor. Using the raw TrustVisor interfaces for PAL
management, you would need to keep track of which address ranges belong to
PAL code, data, etc., and make sure those sections are page-aligned.
Things can get tricky if you want some code to be accessible to both
the PAL code and the application code, and trickier still if you want
to use different implementations for the same function in PAL and
application code (such as linking the PAL against a version of libc
that does not make system calls while linking the regular code with the
standard version of libc).

The TEE-SDK has some tools to take care of these details for you. The
basic approach is use *partial linking* to link all PAL code into a
single object file (.o), rewrite all symbols except for the PAL
entry-point in that object file to be private, and then use a linker
script to link this object file with the regular application while
mapping the code and data of the PAL to special page-aligned sections. The
TrustVisor back-end provides simplified functions for registering a
PAL that has been built and linked this way.

The TEE-SDK includes ``pkg-config`` files that specify the necessary
compilation and link flags, and Makefile snippets that can be included
in your own Makefiles to automate most of the process. Pointing your
makefile at those makefile snippets and\or ``pkg-config`` files (rather
than copying and modifying a monolithic Makefile with these things
hard-coded) will help keep your pal up to date as the build process
evolves. See ``examples/newlib/Makefile`` for
a good starting point of a Makefile that dynamically incorporates the
TEE-SDK-provided Makefile snippets and pkg-config files.

Compiling and running the test example
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

After installation in ``tz``\ , you should be able to compile and run
the test example in ``../examples/test``. Remember to set
the ``PKG_CONFIG_LIBDIR`` environment variable if you installed to a
non-system directory.

Loading and unloading services
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Services are loaded and unloaded through the TrustZone service manager:

.. code-block:: c

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
      eventually it would be good to provide a common abstraction here. */
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

.. code-block:: c

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


Calling services
^^^^^^^^^^^^^^^^

Services are called through the TrustZone API. You must open a session
with a currently-loaded service. A session can be used for multiple
invocations of a service. See the
`TrustZone API specification <http://infocenter.arm.com/help/topic/com.arm.doc.prd29-genc-009492c/PRD29-GENC-009492C_trustzone_security_whitepaper.pdf>`_ for details.

Developing services
^^^^^^^^^^^^^^^^^^^

Service development is currently very trustvisor-specific. 

Memory Layout
^^^^^^^^^^^^^

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
``../tz/conf/pal-template.ld`` for an example of such a linker script.

Service entry point
^^^^^^^^^^^^^^^^^^^

The service entry point should have the following prototype:

.. code-block:: c

   void pal_entry(uint32_t uiCommand,
                  tzi_encode_buffer_t *psInBuf,
                  tzi_encode_buffer_t *psOutBuf,
                  tz_return_t *puiRv)



* ``uiCommand`` will contain command specified in the call to
  ``TZOperationPrepareInvoke``
* ``psInBuf`` will contain the parameters marshalled by ``TZEncode*``. 
  Use the API in [tz/include/marshal.h] to decode this buffer.
* ``psOutBuf`` is an output buffer for marshalled data. Use the
  API in [tz/include/marshal.h] to encode this buffer.
* ``puiRv`` is a status code to be returned. Success should be indicated
  by setting this to ``TZ_SUCCESS``.
