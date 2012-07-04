WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING
===============================================================

You can ruin your motherboard if your BIOS is
buggy. MAKE SURE YOUR BIOS IS UP TO DATE, and use the newest available
SINIT module from Intel (if using an Intel CPU):
<http://software.intel.com/en-us/articles/intel-trusted-execution-technology/>
If you want to be sure your hardware is working, we suggest starting
with Intel's tboot project: <http://tboot.sourceforge.net/>

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

Design Concepts
===============

* [Dynamic Root of Trust for XMHF Launch Integrity](doc/drtm-design.md)
* [Memory Layout and Integrity Checking](doc/memory-layout.md)
