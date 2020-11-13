.. include:: /macros.rst


Installing
==========

Prerequisites
-------------

As a first step, check the :doc:`uberXMHF (pc-intel-x86_32) Hardware Requirements </pc-intel-x86_32/hw-requirements>`\ , and
be sure to enable the corresponding BIOS options (enable TPM, enable VT-x, enable VT-d, and enable TXT--often many of these are disabled by default in the BIOS).
Also make sure your BIOS is up to date; you could ruin your motherboard if your BIOS is buggy.
Secondly, ensure that you are running one of the supported 
guest operating systems (see :doc:`uberXMHF (pc-intel-x86_32) Supported Guest Operating Systems </pc-intel-x86_32/supported-os>`\ -- 32-bit page tables, blacklisted kernel modules ).
Thirdly, ensure you have copied the mico-hypervisor (``xmhf-x86-vmx-x86pc.bin.gz``) and the SINIT module (`Intel TXT webpage <http://software.intel.com/en-us/articles/intel-trusted-execution-technology/>`_) into your `/boot/` directory.
Lastly, configure your system to boot uberXMHF as described below.


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

Booting uberXMHF is currently only supported using Grub 1. If Grub 2 is already
installed (as it typically is on recent Linux distributions), you will
need to downgrade to Grub 1.

The following commands accomplish the above task on Ubuntu:

.. code-block:: bash

   # remove all GRUB 2 files (answer yes to any questions)
   sudo apt-get purge grub-pc grub-common os-prober
   sudo apt-get purge grub-gfxpayload-lists
   sudo apt-get install grub
   # If asked about creating a /boot/grub/menu.lst answer yes
   sudo update-grub
   grub-install /dev/sda


You should have an automatically filled in ``/boot/grub/menu.lst`` with entries for any kernels installed on the machine. While unlikely, check this file for any lines attempting to load GRUB 2 (such as the snippet below):

.. code-block:: bash

   title          Chainload into GRUB 2
   root           b5912383-7f9e-4911-b51d-b14ce8cea70b
   kernel         /boot/grub/core.img


For further details about downgradeing GRUB, please refer to the following posts on `downgrading GRUB for Ubuntu <http://ubuntuforums.org/showthread.php?t=1298932>`_ and `downgrading GRUB for Debian <http://forums.debian.net/viewtopic.php?f=17&t=50132>`_ respectively.

Get the correct SINIT module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

uberXMHF launches itself with a *dynamic root of trust*. On Intel
platforms, this requires a signed SINIT module provided by Intel, that
matches your platform CPU and chipset.

SINIT modules can be found here:
http://software.intel.com/en-us/articles/intel-trusted-execution-technology/

You can determine the appropriate SINIT module by determining your CPU's ``Product Collection`` and ``Code Name``. If unsure about these details. First, find your CPU's model name (``cat /proc/cpuinfo | grep 'model name'``). Second, use the CPU model to search `Intel's product specifications <ark.intel.com>`_. You should now have your CPU's ``Product Collection`` and ``Code Name``, which you can use to identify the appropriate `SINIT module <http://software.intel.com/en-us/articles/intel-trusted-execution-technology/>`_. Note, as of the time of writing, there was a second table at the bottom of the page with the attached SINIT modules (in case the links in the main table do not work).

Ensure that the ``.BIN`` from this module is copied into your ``/boot/`` directory.

Building and Installing uberXMHF binaries
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If you haven't already built and installed uberXMHF, 
see :doc:`Verifying and Building uberXMHF (pc-intel-x86_32) </pc-intel-x86_32/verify-build>`

Ensure that the ``xmhf-x86-vmx-x86pc.bin.gz`` is copied into your ``/boot/`` directory.

Adding a Grub entry to boot Linux
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

You will need to add a Grub entry to ``/boot/grub/menu.lst``. To ensure
that it doesn't get clobbered, put it **outside** the **AUTOMAGIC KERNEL
LIST** (i.e., append it to the end of the file).

To boot a Linux guest, we create a grub entry that loads the
micro-hypervisor, and then re-loads grub. When booting the machine, first
choose the uberXMHF entry, and then choose a normal Linux entry.

A grub entry for uberXMHF should look something like this:

.. code-block:: bash

   title uberXMHF
   uuid   xxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx               # copy this from an AUTOMAGIC entry
   kernel /boot/xmhf-x86-vmx-x86pc.bin.gz serial=115200,8n1,0x3f8 # substitute in the correct serial address
   modulenounzip (hd0)+1                                     # should point to where grub is installed
   modulenounzip /boot/4th_gen_i5_i7_SINIT_75.BIN            # Intel TXT SINIT AC module


This will boot uberXMHF with debug output going to the specified serial
port, and then reload grub.
Note, check if the AUTOMAGIC KERNELS refernce ``/boot/vmlinuz-*`` or simply ``/vmlinuz-*`` and have your uberXMHF entry match (i.e., some do not require the ``/boot/`` prefix in the above example).

Additionally, you must specify new command line options to your guest OS. These options must include ``nmi_watchdog=0``

If your Default OS (the Linux kernel that will be booting after the micro-hypervisor) uses an LVM filesystem, you might need to alter its GRUB entry. Modify the kernel entry to specify the root as the LVM disk. For example, change:


.. code-block:: bash
		
  kernel     /vmlinuz-4.4.236+ root=UUID=xxxxxxxx-xxxx-xxxx-xxxxxxxxxxxx ro quiet splash

  
to

.. code-block:: bash

  kernel      /vmlinuz-4.4.236+ root=/dev/${Volume Group name}/root ro text nomodeset nmi_watchdog=0

  
Where you can find the appropriate ``${Volume Group name}`` using ``sudo vgs --noheadings -o vg_name``

savedefault for unattended boot
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Booting linux involves loading the grub menu twice. The first time you
must select the uberXMHF entry, and the second time you must select an OS
entry. You can automate this by using savedefault.

Set grub to boot the saved default:

.. code-block:: bash

   default         saved


Have your uberXMHF entry and what you want as your default OS entry save
each-other as the new default:

.. code-block:: bash

   title Default OS
   savedefault 1         # where the number equates to the subsequent grub entry to load (i.e. 0 == the first in the list of options)
		
   title uberXMHF
   savedefault 0          


The parameter to savedefault is the menu entry that you would like as
the new default.


Example GRUB `menu.lst`
^^^^^^^^^^^^^^^^^^^^^^^

A minimal grub ``menu.lst`` example is shown below.

.. code-block:: bash
 
default saved

title          Default OS
uuid           c8abe43f-8658-42bb-b238-60b97320c50
kernel         /vmlinuz-4.4.236+ root=/dev/uberXMHF-vg/root ro text nomodeset memblock=debug nmi_watchdog=0
initrd         /initrd.img-4.4.236+
savedefault    1

title          uberXMHF
uuid           c8abe43f-8658-42bb-b238-60b97320c50
kernel         /xmhf-x86-vmx-x86pc.bin.gz serial=11520,8n1,0x3f8
modulenounzip  (hd0)+1
modulenounzip  /4th_gen_i5_i7_SINIT_75.BIN
savedefault    0

