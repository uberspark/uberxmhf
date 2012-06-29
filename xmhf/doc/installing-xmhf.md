Configure hardware
==================

Check the [XMHF Hardware Requirements](hardware-requirements.md), and
be sure to enable the corresponding BIOS options.

Supported guest operating systems
=================================

In principle, any guest should be supported so long as it:

* Uses 'normal' 32-bit page tables. PAE is also supported on
  AMD. 64-bit is not yet supported.
* Does not use MTRRs. XMHF does not yet virtualize these (on Intel
  platforms), and an attempt by the guest to access MTRRs will trap
  and halt the system.

The following guest OSes are known to work:

* Windows XP
* Windows Server 2003
* Ubuntu 10.04 (with custom kernel to disable MTRRs. See [Custom Linux
  Kernels](custom-linux-kernels.md))

Obtain XMHF binaries
====================

If you haven't already built XMHF, see [Building XMHF](building-xmhf.md)

Install XMHF binaries
=====================

If you have a .deb, use `dpkg -i` to install it. Otherwise, copy
`init-x86.bin` and `hypervisor-x86.bin.gz` to `/boot`.

Configure your system to boot XMHF
==================================

You will need to install Grub 1, if you haven't already. On most
modern Linux distributions, you will need to downgrade from Grub 2. On
Windows machines without a Linux installation, you will need to
install Grub. This can be done by installing a minimal Linux
installation, which will typically take care of non-destructively
repartitioning for you.

See [Configuring Grub](configuring-grub.md) for how to add an XMHF
entry to Grub.
