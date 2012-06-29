Introduction
============

XMHF is a modular hypervisor platform for recent multicore x86
hardware with support for dynamic root of trust and nested
(2-dimensional) paging.  It is NOT a full virtual machine monitor.

XMHF takes a developer-centric approach to hypervisor design and
implementation, and strives to be a comprehensible and flexible
platform for performing hypervisor research and development. XMHF
encapsulates common hypervisor core functionality in a framework that
allows others to build custom hypervisor-based solutions (called
"hypapps"). It currently supports only a single "rich" guest OS.

Quick start to using XMHF
=========================

* [XMHF Hardware Requirements](doc/hardware-requirements.md)
* [Building XMHF](doc/building-xmhf.md)
* [Installing XMHF](doc/installing-xmhf.md)
* [Configuring Grub](doc/configuring-grub.md) How to boot XMHF from
  Grub, along with some tricks for remote\unattended boot.
* [Custom Linux Kernels](doc/custom-linux-kernels.md)
* [Debugging XMHF](doc/debugging-xmhf.md)

