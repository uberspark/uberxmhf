Introduction
============

XMHF is an eXtensible and Modular Hypervisor Framework 
that strives to be a
comprehensible and flexible platform for performing 
hypervisor research and development. The framework allows others to 
build custom (security-sensitive) hypervisor-based solutions 
(called "hypapps").

XMHF is designed to achieve three goals – modular extensibility,
automated verification, and high performance. XMHF includes a
core that provides functionality common to many hypervisor-based security
architectures and supports extensions that augment the core with
additional security or functional properties while preserving the 
fundamental hypervisor security property of memory integrity 
(i.e., ensuring that the hypervisor’s memory is not modified by 
software running at a lower privilege level).

XMHF advocates a "rich" single-guest execution model where the 
hypervisor framework supports only a single-guest and allows the 
guest direct access to all performance-critical system devices and 
device interrupts.

XMHF currently runs on recent multicore x86 hardware 
virtualized platforms with support for dynamic root of trust 
and nested (2-dimensional) paging. The framework is capable of
running unmodified legacy multiprocessor capable OSes such as 
Windows and Linux.  


Quick start to using XMHF
=========================

* [XMHF Hardware Requirements](doc/hardware-requirements.md)
* [Building XMHF](doc/building-xmhf.md)
* [Verifying XMHF](doc/verifying-xmhf.md)
* [Installing XMHF](doc/installing-xmhf.md)
* [Configuring Grub](doc/configuring-grub.md) How to boot XMHF from
  Grub, along with some tricks for remote\unattended boot.
* [Debugging XMHF](doc/debugging-xmhf.md)

