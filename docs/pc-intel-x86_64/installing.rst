.. include:: /macros.rst


Installing
==========

Prerequisites
-------------

As a first step, check the :doc:`uberXMHF (pc-intel-x86_64) Hardware Requirements </pc-intel-x86_64/hw-requirements>`\ , and
be sure to enable the corresponding BIOS options. Also make sure your
BIOS is up to date; you could ruin your motherboard if your BIOS is
buggy. Secondly, ensure that you are running one of the supported 
guest operating systems (see :doc:`uberXMHF (pc-intel-x86_64) Supported Guest 
Operating Systems </pc-intel-x86_64/supported-os>`\ ).
Lastly, configure your system to boot uberXMHF (pc-intel-x86_64) as 
described below.

Configure target system to boot uberXMHF
----------------------------------------

You will need to install Grub 2, if you haven't already. On most
modern Linux distributions, you already have Grub 2. On
Windows machines without a Linux installation, you will need to
install Grub. This can be done by installing a minimal Linux
installation, which will typically take care of non-destructively
repartitioning for you.

Get the correct SINIT module (Intel only)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

uberXMHF (pc-intel-x86_64) launches itself with a *dynamic root of trust*. 
On Intel
platforms, this requires a signed SINIT module provided by Intel, that
matches your platform CPU and chipset.

SINIT modules can be found here:
http://software.intel.com/en-us/articles/intel-trusted-execution-technology/

Building and Installing uberXMHF (pc-intel-x86_64) binaries
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If you haven't already built and installed uberXMHF (pc-intel-x86_64), 
see :doc:`Building uberXMHF (pc-intel-x86_64) </pc-intel-x86_64/build>`

Booting sequence
^^^^^^^^^^^^^^^^

GRUB 2 will be used to launch XMHF-64 and to launch the guest operating system.
This usually requires the user to select different menu entries in GRUB.

GRUB 2 needs to be launched by BIOS. EFI / UEFI is not supported. This means
that XMHF likely does not work on disks formatted as GPT (XMHF works on MBR).

The boot sequence is:

1. The machine starts, BIOS starts running
2. BIOS launches GRUB
3. GRUB launches XMHF-64 (selected by the user)
4. XMHF-64 launches GRUB in virtual machine mode (e.g. Intel VMX)
5. GRUB launches guest OS (selected by the user)

Install files
^^^^^^^^^^^^^

The build process will generate the following files, where ``$(SUBARCH)`` is
``i386`` (for 32-bit uberXMHF) or ``amd64`` (for 64-bit uberXMHF). Copy these
files to ``/boot/`` of the operating system. These files will be accessed by
GRUB.

.. code-block:: text

   init-x86-$(SUBARCH).bin
   hypervisor-x86-$(SUBARCH).bin.gz

Adding a Grub entry
^^^^^^^^^^^^^^^^^^^

A menuentry needs to be added to GRUB. For Debian it is done by adding a file
with execute permission in ``/etc/grub.d/``. For example, create a file at
``/etc/grub.d/42_xmhf_i386``:

.. code-block:: bash

   #!/bin/sh
   exec tail -n +3 $0
   # This file provides an easy way to add custom menu entries.  Simply type the
   # menu entries you want to add after this comment.  Be careful not to change
   # the 'exec tail' line above.

   menuentry "XMHF-i386" {
       set root='(hd0,msdos1)'  # point to file system for /
       set kernel='/boot/init-x86-i386.bin'
       set boot_drive='0x80'    # should point to where grub is installed
       echo "Loading ${kernel}..."
       multiboot ${kernel} serial=115200,8n1,0x5080 boot_drive=${boot_drive}
       module /boot/hypervisor-x86-i386.bin.gz
       module --nounzip (hd0)+1 # should point to where grub is installed
       module /boot/i5_i7_DUAL_SINIT_51.BIN
   }

Please following the line by line explanation of the file above to edit it

*
  ``#!/bin/sh`` and ``exec tail -n +3 $0``: this executable file will print the
  content starting at line 3. Don't touch them.

*
  ``menuentry "XMHF-i386" {``: "XMHF-i386" will be the entry name in GRUB. This
  name can be changed freely.

*
  ``set root='(hd0,msdos1)'``: set partition of the operating system. This
  partition is used to access XMHF files. ``(hd0,msdos1)`` is first disk's
  first MBR partition. See GRUB's documentation.

* ``set kernel='/boot/init-x86-i386.bin'``: set XMHF bootloader file. Change
  ``init-x86-i386.bin`` to ``init-x86-amd64.bin`` for amd64 XMHF.

	*
	  In the example configuration, GRUB should find a MBR partition on the
	  first hard drive (hd0). The partition should contain a file system with
	  a directory called ``boot`` at the root, and this directory should
	  contain the file ``init-x86-i386.bin``.

*
  ``set boot_drive='0x80'``: specify the disk where XMHF can find GRUB.
  ``0x80`` is the first hard disk (corresponding to ``hd0``), ``0x81`` is the
  second hard disk (``hd1``), etc. Usually this does not need to change if you
  are only working with only one hard disk.

*
  ``echo "Loading ${kernel}..."``: just printing a message, no need to change.

*
  ``multiboot ${kernel} serial=115200,8n1,0x5080 boot_drive=${boot_drive}``:
  specify multiboot kernel to be the XMHF bootloader

	*
	  ``serial=115200,8n1,0x5080``: specify serial parameters. The parameters
	  can usually be found by running ``dmesg | grep ttyS`` in Linux. For
	  example you may see
	  ``... ttyS0 at I/O 0x5080 (irq = 17, base_baud = 115200) is a 16550A``.

*
  ``module /boot/hypervisor-x86-i386.bin.gz``: load the first multiboot module,
  which must be XMHF secureloader and runtime. Again change it to
  ``hypervisor-x86-amd64.bin.gz`` if running amd64 XMHF.

*
  ``module --nounzip (hd0)+1``: specify the disk where XMHF can find GRUB.
  ``(hd0)`` is the first hard disk, and ``+1`` means 1 block since offset 0
  (this is GRUB's block list syntax). Usually this does not need to change if
  you are only working with only one hard disk.

*
  ``module /boot/i5_i7_DUAL_SINIT_51.BIN``: For a Intel machine with DRT
  enabled, this is the SINIT AC Module downloaded from Intel's website. Make
  sure to select the file that matches your machine's CPU. When DRT is
  disabled, this line can be removed.

After the modification is done, make sure it is executable and update GRUB.

.. code-block:: bash

   chmod +x /etc/grub.d/42_xmhf_i386
   update-grub

Multiple disks
^^^^^^^^^^^^^^

It may be convenient to install GRUB on one disk and the guest operating system
on another. Consider this scenario: we have installed XMHF on a USB, and we
want to test it on an OS installed on a HDD.

The partition table of USB looks like:

+------------+---------------------------------------------+
| MBR header | Partition 1: ext4                           |
+------------+---------------------------------------------+
| GRUB       | XMHF installed in /boot/                    |
+------------+---------------------------------------------+

The partition table of HDD looks like:

+------------+-----------------------+---------------------+
| MBR header | Partition 1: ???      | Partition 2: ???    |
+------------+-----------------------+---------------------+
| Bootloader | Guest OS              | ...                 |
+------------+-----------------------+---------------------+

The target computer by default only has the HDD connected. When a BIOS boots
the HDD, it will set DL=0x80, and ``(hd0)`` is HDD. When a USB is inserted, the
USB is ``(hd1)``.

However, if the BIOS boots the USB, then the USB becomes ``(hd0)`` and the HDD
becomes ``(hd1)``. The BIOS will still set DL=0x80.

Suppose we want to make the boot sequence "BIOS -> USB GRUB -> XMHF -> HDD
Bootloader". Then USB GRUB should find the HDD Bootloader at ``(hd1)``, and HDD
bootloader should be passed DL=0x81. So the configuration file should be

.. code-block:: bash

   #!/bin/sh
   ...
   menuentry "XMHF-i386" {
       ...
       set boot_drive='0x81'
       ...
       module --nounzip (hd1)+1
       ...
   }

