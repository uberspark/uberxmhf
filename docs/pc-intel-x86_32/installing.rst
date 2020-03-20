.. role:: raw-html-m2r(raw)
   :format: html


----

layout: page
tocref: uber eXtensible Micro-Hypervisor Framework Documentation &gt; pc-intel-x86_32 

title: Installing
-----------------

Prerequisites
-------------

As a first step, check the :doc:`uberXMHF (pc-intel-x86_32) Hardware Requirements <{% link docs/pc-intel-x86_32/hw-requirements>`\ , and
be sure to enable the corresponding BIOS options. Also make sure your
BIOS is up to date; you could ruin your motherboard if your BIOS is
buggy. Secondly, ensure that you are running one of the supported 
guest operating systems (see :doc:`uberXMHF (pc-intel-x86_32) Supported Guest Operating Systems <{% link docs/pc-intel-x86_32/supported-os>`\ ).
Lastly, configure your system to boot uberXMHF as described below.

:raw-html-m2r:`<br/>`

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

.. code-block::

   sudo apt-get purge grub* os-prober
   sudo apt-get purge grub-gfxpayload-lists
   sudo apt-get install grub
   sudo update-grub
   grub-install /dev/sda


And remove lines (if any) from ``/boot/grub/menu.lst``\ :

.. code-block::

   title          Chainload into GRUB 2
   root           b5912383-7f9e-4911-b51d-b14ce8cea70b
   kernel         /boot/grub/core.img


For further details refer to the following posts on `downgrading GRUB for Ubuntu <http://ubuntuforums.org/showthread.php?t=1298932>`_ and `downgrading GRUB for Debian <http://forums.debian.net/viewtopic.php?f=17&t=50132>`_ respectively.

Get the correct SINIT module
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

uberXMHF launches itself with a *dynamic root of trust*. On Intel
platforms, this requires a signed SINIT module provided by Intel, that
matches your platform CPU and chipset.

SINIT modules can be found here:
http://software.intel.com/en-us/articles/intel-trusted-execution-technology/

Building and Installing uberXMHF binaries
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If you haven't already built and installed uberXMHF, 
see :doc:`Verifying and Building uberXMHF (pc-intel-x86_32) <{% link docs/pc-intel-x86_32/verify-build>`

Adding a Grub entry to boot Linux
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

You will need to add a Grub entry to ``/boot/grub/menu.lst``. To ensure
that it doesn't get clobbered, put it **\ *outside the AUTOMAGIC KERNEL
LIST*\ **.

To boot a Linux guest, we create a grub entry that loads the
hypervisor, and then re-loads grub. When booting the machine, first
choose the uberXMHF entry, and then choose a normal Linux entry.

A grub entry for uberXMHF should look something like this:

.. code-block::

   title uberXMHF
   rootnoverify (hd0,1)                                      # should point to /boot
   kernel /boot/xmhf-x86-vmx-x86pc.bin.gz serial=115200,8n1,0x3f8 # substitute in the correct serial address
   modulenounzip (hd0)+1                                     # should point to where grub is installed
           modulenounzip /boot/4th_gen_i5_i7_SINIT_75.BIN            # Intel TXT AC SINIT module


This will boot uberXMHF with debug output going to the specified serial
port, and then reload grub.

savedefault for unattended boot
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Booting linux involves loading the grub menu twice. The first time you
must select the uberXMHF entry, and the second time you must select an OS
entry. You can automate this by using savedefault.

Set grub to boot the saved default:

.. code-block::

   default         saved


Have your uberXMHF entry and what you want as your default OS entry save
each-other as the new default:

.. code-block::

   title uberXMHF
       savedefault 1

   title Default OS
       savedefault 0


The parameter to savedefault is the menu entry that you would like as
the new default.
