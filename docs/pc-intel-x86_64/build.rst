.. include:: /macros.rst

.. _pc-intel-x86_64-building:

Building
========

uberXMHF (pc-intel-x86_64) and uberapps (e.g., :doc:`TrustVisor </pc-intel-x86_64/uberapp-trustvisor>`\ ) get built 
in a Linux environment with 
a recent version of gcc. uberXMHF (pc-intel-x86_64) has been verified to 
build on Debian 11 and Fedora 35, both 32 and 64 bit.

It is also possible to build uberXMHF in docker. The ``debian:11`` Docker tag is known to work.

Build tools
-----------

A (partial) list of packages to install on Ubuntu / Debian:

.. code-block:: bash

   aptitude install pbuilder texinfo ruby build-essential autoconf libtool

A (partial) list of packages to install on Fedora:

.. code-block:: bash

   dnf install autoconf automake make gcc
   # The next line installs fallocate, which is recommended
   dnf install util-linux

On 64-bit Debian, you will also need to install 32-bit libraries:

.. code-block:: bash

   aptitude install build-essential crossbuild-essential-i386

On 32-bit Debian, to compile XMHF in 64-bit, install 64-bit cross compiler:

.. code-block:: bash

   apt-get install build-essential crossbuild-essential-amd64

High-level Build Summary
------------------------

One "drives" the build from the root directory of uberXMHF (pc-intel-x86_64):

The interesting high-level build commands include:

.. code-block:: bash

   ./autogen.sh           # creates ./configure
   ./configure            # creates Makefile from Makefile.in
   make                   # builds the selected hypapp and the XMHF core
   make install           # installs binaries
   make install-dev       # (hypapp specific) installs dev headers and libs
   make test              # (hypapp specific) runs various automated tests
   make clean             # cleanup
   make htmldoc           # generates the HTML documentation you are reading in the `./doc` sub-folder


The functioning of ``make install-dev`` and ``make test`` are
uberapp-specific. For example, in the TrustVisor uberapp, the primary prerequisite
for tee-sdk and PAL development is having successfully run 
``make install-dev``.

How do I build a uberXMHF (pc-intel-x86_64) uberapp?
-----------------------------------------------------

The method for building different uberapps (e.g., TrustVisor) is by specifying
which uberapp to build using ``./configure``.
The following describes the sequence of steps for building a 
uberXMHF (pc-intel-x86_64) uberapp using the helloworld 
uberapp as a running example.

Change working directory to the uberXMHF (pc-intel-x86_64) root directory.

.. code-block:: bash

   cd ./xmhf-64


Generate the ``./configure`` script.

.. code-block:: bash

   ./autogen.sh


Configure the uberXMHF (pc-intel-x86_64) uberapp (see below for the
``--with-target-subarch=`` configuration option).

.. code-block:: bash

   ./configure --with-approot=hypapps/helloworld --with-target-subarch=...


Generate and install the binaries:

.. code-block:: bash

   make
   make install
   make install-dev  # optional (hypapp-specific)
   make test         # optional (hypapp-specific)


To use multiple processors on the compiling machine, try ``make -j $(nproc)``.

Note that ``make install`` is only useful if the development system and 
the target system (on which uberXMHF (pc-intel-x86_64) is installed) are 
the same. If not, 
you will need to manually copy the files ``./xmhf/init-x86.bin`` 
and ``./xmhf/hypervisor-x86.bin.gz`` to the ``/boot`` folder of the
target system (see :doc:`Installing uberXMHF (pc-intel-x86_64) </pc-intel-x86_64/installing>` ).  

Build configuration options
---------------------------

Mandatory arguments
^^^^^^^^^^^^^^^^^^^

* 
  --with-approot=[UBERAPP_PATH], specifies the uberapp source root; must be provided

*
  --with-target-subarch=[TARGET_SUBARCH], specify which subarch of uberXMHF to
  build (32-bit or 64-bit); must be provided

	*
	  When building 32-bit uberXMHF on 32-bit Debian or Fedora:
	  ``--with-target-subarch=i386``
	*
	  When building 64-bit uberXMHF on 32-bit Debian:
	  ``--with-target-subarch=amd64 CC=x86_64-linux-gnu-gcc LD=x86_64-linux-gnu-ld``
	*
	  When building 64-bit uberXMHF on 32-bit Fedora:
	  ``--with-target-subarch=amd64``
	* 
	  When building 32-bit uberXMHF on 64-bit Debian:
	  ``--with-target-subarch=i386 CC=i686-linux-gnu-gcc LD=i686-linux-gnu-ld``
	*
	  When building 32-bit uberXMHF on 64-bit Fedora:
	  ``--with-target-subarch=i386``
	*
	  When building 64-bit uberXMHF on 64-bit Debian or Fedora:
	  ``--with-target-subarch=amd64``
	*
	  If these argument is not added correctly, an error message like
	  ``ld: cannot find -lgcc`` may appear when building.

* 
  --with-target-platform=[PLATFORM], specifies the target platform for the build; 
  optional, current options are: x86pc (x86 hardware virtualized platforms, default)

* 
  --with-target-arch=[ARCH], specifies the target CPU architecture; 
  optional, current options are: x86vmx (Intel, default)

Recommended arguments
^^^^^^^^^^^^^^^^^^^^^

*
  --enable-debug-symbols, adds debug info to generated ELF files. With this
  configuration, GDB can print symbols in ``*.exe`` files.

*
  --disable-drt, disables Dynamic Root-of-Trust (DRT); optional, useful for builds 
  targeting platforms without support for DRT and/or TPM

*
  --disable-dmap, disables DMA protection; optional, useful for builds targeting 
  platforms without DMA protection capabilities

*
  --with-amd64-max-phys-addr=[MAX_PHYS_ADDR], configures maximum physical
  address (in bytes) supported by 64-bit uberXMHF

	*
	  For example, ``--with-amd64-max-phys-addr=0x140000000`` sets physical
	  address to 5 GiB. The default is 16 GiB. When XMHF runs on a machine that
	  has more physical memory than this value, XMHF will halt. This
	  configuration is ignored in i386 XMHF

*
  --enable-update-intel-ucode, allows the guest to perform microcode update

Other arguments
^^^^^^^^^^^^^^^

*
  --disable-debug-serial --enable-debug-vga, print debug messages on VGA, not
  serial port. This is useful for builds targeting platforms without serial
  ports

*
  --with-opt=[COMPILER_FLAGS], compiles XMHF with optimization. For example,
  ``--with-opt='-O3 -Wno-stringop-overflow'`` adds ``-O3`` and
  ``-Wno-stringop-overflow`` to GCC's arguments to compile in optimization
  ``-O3``. As of writing of this documentation, ``-Wno-stringop-overflow`` is
  needed due to a `bug <https://gcc.gnu.org/bugzilla/show_bug.cgi?id=105100>`_
  in GCC:

*
  --enable-optimize-nested-virt, enables some risky optimizations in intercept
  handling

	*
	  When running XMHF under many levels of nested virtualization, VMREAD and
	  VMWRITE instructions become expensive. This configuration enables
	  manually optimized intercept handling for some cases to prevent XMHF from
	  running too slow to boot the guest OS. However, these optimizations need
	  to be manually maintained and may be incorrect.

Configuration examples
^^^^^^^^^^^^^^^^^^^^^^

``xmhf-64/.github/build.sh`` can be used to generate configuration options. It
automatically detects the compiling machine's bit size and can be especially
helpful to figure out cross-compile options. See comments at the start of this
file. The following will print sample configuration commands:

.. code-block:: bash

   ./.github/build.sh i386 release -n
   ./.github/build.sh amd64 release -n

Other examples:

.. code-block:: bash

   # Build i386 XMHF on i386 Ubuntu, without DRT and DMAP
   ./configure --with-approot=hypapps/trustvisor --disable-dmap --disable-drt

   # Build i386 on amd64 Debian
   ./configure --with-approot=hypapps/trustvisor --enable-debug-symbols --enable-debug-qemu CC=i686-linux-gnu-gcc LD=i686-linux-gnu-ld

   # Build amd64 on amd64 Debian, with 8 GiB memory, and use VGA instead of serial
   ./configure --with-approot=hypapps/trustvisor --with-target-subarch=amd64 --enable-debug-symbols --enable-debug-qemu --with-amd64-max-phys-addr=0x200000000 --disable-debug-serial --enable-debug-vga

