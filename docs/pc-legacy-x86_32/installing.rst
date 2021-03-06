.. include:: /macros.rst


Installing
==========

Prerequisites
-------------

As a first step, check the :doc:`uberXMHF (pc-legacy-x86_32) Hardware Requirements </pc-legacy-x86_32/hw-requirements>`\ , and
be sure to enable the corresponding BIOS options. Also make sure your
BIOS is up to date; you could ruin your motherboard if your BIOS is
buggy. Secondly, ensure that you are running one of the supported 
guest operating systems (see :doc:`uberXMHF (pc-legacy-x86_32) Supported Guest 
Operating Systems </pc-legacy-x86_32/supported-os>`\ ).
Lastly, configure your system to boot uberXMHF (pc-legacy-x86_32) as 
described below.

Configure target system to boot uberXMHF
----------------------------------------

You will need to install Grub 1, if you haven't already. On most
modern Linux distributions, you will need to downgrade from Grub 2. On
Windows machines without a Linux installation, you will need to
install Grub. This can be done by installing a minimal Linux
installation, which will typically take care of non-destructively
repartitioning for you.

Downgrade from Grub 2 to Grub 1
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Booting uberXMHF (pc-legacy-x86_32) is currently only supported 
using Grub 1. If Grub 2 is already
installed (as it typically is on recent Linux distributions), you will
need to downgrade to Grub 1.

The following commands accomplish the above task on Ubuntu:

.. code-block:: bash

   sudo apt-get purge grub* os-prober
   sudo apt-get purge grub-gfxpayload-lists
   sudo apt-get install grub
   sudo update-grub
   grub-install /dev/sda


And remove lines (if any) from ``/boot/grub/menu.lst``\ :

.. code-block:: bash

   title          Chainload into GRUB 2
   root           b5912383-7f9e-4911-b51d-b14ce8cea70b
   kernel         /boot/grub/core.img


For further details refer to the following posts on `downgrading GRUB for Ubuntu <http://ubuntuforums.org/showthread.php?t=1298932>`_ and `downgrading GRUB for Debian <http://forums.debian.net/viewtopic.php?f=17&t=50132>`_ respectively.

Get the correct SINIT module (Intel only)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

uberXMHF (pc-legacy-x86_32) launches itself with a *dynamic root of trust*. 
On Intel
platforms, this requires a signed SINIT module provided by Intel, that
matches your platform CPU and chipset.

SINIT modules can be found here:
http://software.intel.com/en-us/articles/intel-trusted-execution-technology/

Building and Installing uberXMHF (pc-legacy-x86_32) binaries
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If you haven't already built and installed uberXMHF (pc-legacy-x86_32), 
see :doc:`Building uberXMHF (pc-legacy-x86_32) </pc-legacy-x86_32/verify-build>`

Adding a Grub entry
^^^^^^^^^^^^^^^^^^^

You will need to add a Grub entry to ``/boot/grub/menu.lst``. To ensure
that it doesn't get clobbered, put it **outside** the **AUTOMAGIC KERNEL
LIST**.

Grub entry to boot Linux
^^^^^^^^^^^^^^^^^^^^^^^^

To boot a Linux guest, we create a grub entry that loads the
hypervisor, and then re-loads grub. When booting the machine, first
choose the uberXMHF (pc-legacy-x86_32) entry, and then choose a 
normal Linux entry.

A grub entry for uberXMHF (pc-legacy-x86_32) should look something like this:

.. code-block:: bash

   title uberXMHF (pc-legacy-x86_32)
       rootnoverify (hd0,1)                         # should point to /boot
       kernel /init-x86.bin serial=115200,8n1,0x3f8 # substitute in the correct serial address
       module /hypervisor-x86.bin.gz
       modulenounzip (hd0)+1                        # should point to where grub is installed


On Intel it is necessary to append one more line to provide the SINIT
Authenticated Code module, or "ACmod". This should be the *last*
line. E.g.,

.. code-block:: bash

       module /i5_i7_DUAL_SINIT_18.BIN


This will boot uberXMHF (pc-legacy-x86_32) with debug output going to 
the specified serial
port, and then reload grub.

Grub entry to boot Windows
^^^^^^^^^^^^^^^^^^^^^^^^^^

To boot Windows, configure uberXMHF (pc-legacy-x86_32) to load the 
Windows boot sector
instead of recursively loading grub. Do this by modifying the
``modulenounzip`` line to point to the partition where Windows is
installed instead of pointing to the MBR. For example, if Windows is
installed on ``/dev/sda3``\ :

.. code-block:: bash

   title Windows on uberXMHF (pc-legacy-x86_32)
       rootnoverify (hd0,1)                         # should point to /boot
       kernel /init-x86.bin serial=115200,8n1,0x3f8 # substitute in the correct serial address
       module /hypervisor-x86.bin.gz
       modulenounzip (hd0,2)+1                        # point to Windows partition


The rest of the settings are the same as for Linux, above. Again, you
will need to add a line for the SINIT module on Intel platforms.

savedefault for unattended boot
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Booting linux involves loading the grub menu twice. The first time you
must select the uberXMHF (pc-legacy-x86_32) entry, and the second time 
you must select an OS
entry. You can automate this by using savedefault.

Set grub to boot the saved default:

.. code-block:: bash

   default         saved


Have your uberXMHF (pc-legacy-x86_32) entry and what you want as your 
default OS entry save
each-other as the new default:

.. code-block:: bash

   title uberXMHF (pc-legacy-x86_32)
       savedefault 1

   title Default OS
       savedefault 0


The parameter to savedefault is the menu entry that you would like as
the new default.
