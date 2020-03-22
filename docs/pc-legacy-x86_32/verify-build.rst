.. include:: /macros.rst

.. _pc-legacy-x86_32-verifybuilding:

Verifying and Building
======================

Verifying
---------

One of the main design goals of uberXMHF (pc-legacy-x86_32) is to achieve 
automated verification
while coping with implementation changes as a result of development.
The uberXMHF (pc-legacy-x86_32) core provides functionality common to many hypervisor-based 
security architectures and supports hypapps that augment the core with
additional security or functional properties while preserving the 
fundamental hypervisor security property of memory integrity 
(i.e., ensuring that the hypervisor’s memory is not modified by 
software running at a lower privilege level).

We have verified the memory integrity of the uberXMHF (pc-legacy-x86_32) core
using a combination of automated and manual techniques.
The model checker `CBMC <http://www.cprover.org/cbmc>`_ is employed for 
automatic verification.
Manual audits apply to a small portion of the code which we anticipate 
to remain mostly unchanged as
development proceeds. The manual audits include constructs
that CBMC cannot verify, including loops that iterate over
entire page tables, platform hardware initialization and interaction,
and concurrent threads coordinating multiple CPUs during initialization
that are challenging for current model-checkers. For more details
please refer to our 2013 IEEE Security and Privacy `paper <http://hypcode.org/paper-xmhf-IEEES&P-2013.pdf>`_.

Verification Environment and Tools
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

OS: Ubuntu 10.10, 32-bit; Available `here <http://old-releases.ubuntu.com/releases/maverick/ubuntu-10.10-desktop-i386.iso>`_

Verification Tools: 
CBMC: v4.1 32-bit; Available `here <http://www.cprover.org/cbmc/download/cbmc_4.1_i386.deb>`_

Install using: 

.. code-block:: bash

   sudo dpkg -i cbmc_4.1_i386.deb



How do I verify uberXMHF (pc-legacy-x86_32) and/or a uberapp?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Configure and build uberXMHF (pc-legacy-x86_32)/uberapp as described in 
the :ref:`Building`
section below. The following describe the specific steps to verify the 
uberXMHF (pc-legacy-x86_32) core memory integrity using the example 
verify uberapp.

Change working directory to the uberXMHF (pc-legacy-x86_32) source tree root.

.. code-block:: bash

   cd ./xmhf


Generate the ``./configure`` script.

.. code-block:: bash

   ./autogen.sh


Configure the XMHF verify hypapp.

.. code-block:: bash

   ./configure --with-approot=hypapps/verify 


Verify

.. code-block:: bash

   make verifyall
   or
   make verify


``make verifyall`` will perform full verification of the 
uberXMHF (pc-legacy-x86_32) core
as well as the uberapp. Subsequently, you can use ``make verify`` to 
verify the uberapp assuming there are no further changes to the 
uberXMHF (pc-legacy-x86_32) core.

Note that we assume CBMC is sound. i.e., if CBMC
reports a successful verification, then uberXMHF (pc-legacy-x86_32)/uberapp 
preserve 
memory integrity.

For verification purposes, we also assume that a uberapp built on top 
of uberXMHF (pc-legacy-x86_32) uses the prescribed core APIs and that 
it does not write to arbitrary
code and data. In fact, these are the only assumptions
required of any new uberapp to ensure the memory integrity
property of uberXMHF (pc-legacy-x86_32). 
In the current uberXMHF (pc-legacy-x86_32) implementation, a single 
core API function ``xmhf_memprot_setprot``
allows manipulating guest memory protections
via 2nd level hardware page tables. 


Building
--------

uberXMHF (pc-legacy-x86_32) and uberapps (e.g., :doc:`TrustVisor </pc-legacy-x86_32/uberapp-trustvisor>`\ , 
:doc:`Lockdown </pc-legacy-x86_32/uberapp-lockdown>`\ ) get built 
in a Linux environment with 
a recent version of gcc. uberXMHF (pc-legacy-x86_32) has been verified to 
build on Ubuntu 10, 11, and 12 series, both 32 and 64 bit.

Build tools
^^^^^^^^^^^

A (partial) list of packages to install:

.. code-block:: bash

   aptitude install pbuilder texinfo ruby build-essential autoconf libtool


On 64-bit platforms, you will also need to install 32-bit
libraries. On Ubuntu 12:

.. code-block:: bash

   aptitude install gcc-multilib



High-level Build Summary
^^^^^^^^^^^^^^^^^^^^^^^^

One "drives" the build from the root directory of uberXMHF (pc-legacy-x86_32):

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

How do I build a uberXMHF (pc-legacy-x86_32) uberapp?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The method for building different uberapps (e.g., TrustVisor,
Lockdown) is by specifying which uberapp to build using ``./configure``.
The following describes the sequence of steps for building a 
uberXMHF (pc-legacy-x86_32) uberapp using the helloworld 
uberapp as a running example.

Change working directory to the uberXMHF (pc-legacy-x86_32) root directory.

.. code-block:: bash

   cd ./xmhf


Generate the ``./configure`` script.

.. code-block:: bash

   ./autogen.sh


Configure the uberXMHF (pc-legacy-x86_32) uberapp.

.. code-block:: bash

   ./configure --with-approot=hypapps/helloworld


Generate and install the binaries:

.. code-block:: bash

   make
   make install
   make install-dev  # optional (hypapp-specific)
   make test         # optional (hypapp-specific)


Note that ``make install`` is only useful if the development system and 
the target system (on which uberXMHF (pc-legacy-x86_32) is installed) are 
the same. If not, 
you will need to manually copy the files ``./xmhf/init-x86.bin`` 
and ``./xmhf/hypervisor-x86.bin.gz`` to the ``/boot`` folder of the
target system (see :doc:`Installing uberXMHF (pc-legacy-x86_32) </pc-legacy-x86_32/installing>` ).  

Build configuration options
^^^^^^^^^^^^^^^^^^^^^^^^^^^


* 
  --with-approot=[UBERAPP_PATH], specifies the uberapp source root; must be provided

* 
  --with-target-platform=[PLATFORM], specifies the target platform for the build; 
  optional, current options are: x86pc (x86 hardware virtualized platforms, default)

* 
  --with-target-arch=[ARCH], specifies the target CPU architecture; 
  optional, current options are: x86vmx (Intel, default), x86svm (AMD)

* 
  --disable-drt, disables Dynamic Root-of-Trust (DRT); optional, useful for builds 
  targeting platforms without support for DRT and/or TPM

* 
  --disable-dmap, disables DMA protection; optional, useful for builds targeting 
  platforms without DMA protection capabilities
