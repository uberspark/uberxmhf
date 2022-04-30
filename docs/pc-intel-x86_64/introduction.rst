.. include:: /macros.rst


Introduction
============

XMHF-64 is branch of XMHF that supports running XMHF in both 32-bit and 64-bit.
32-bit is called "i386" and 64-bit is called "amd64". This bit width difference
is called "subarch".

XMHF-64 has 3 phases: bootloader, secureloader, and runtime. Bootloader will
always run in i386. Secureloader and runtime will run in the subarch as
configured by the user (i386 or amd64). Only amd64 XMHF-64 can run amd64 guest
operating systems. A comparision is below.

===============  ===============  =======================
Name             XMHF-64 in i386  XMHF-64 in amd64
===============  ===============  =======================
bootloader       i386             i386
secureloader     i386             amd64
runtime          i386             amd64
guest OS         i386 (no PAE)    i386 or amd64
physical memory  4 GiB            >= 4 GiB (configurable)
===============  ===============  =======================

Features
--------

Compared to XMHF, the main features of XMHF-64 are

* Fix compile errors found in high GCC version
* Support running XMHF in 64-bit mode
* Support continuous integration testing
* Support running XMHF in QEMU
* Support running XMHF with modern guest operating systems
* Support running guests that use PAE paging
* Provide ``pal_demo``

    * Allows running code for TrustVisor without writing linker scripts
    * Provides a wrapper to run TrustVisor code in Windows

* Optimization on the build process

	* Decrease artifact size
	* Support Optimized compile (e.g. ``-O3``)

* Support DMAP in Intel
* Allow the guest OS to change MTRR
* Support x2APIC

Bugs
----

While developing XMHF-64, the following bugs are found in XMHF

*
  ``dealwithE820()`` does not check ``grube820list_numentries``, which may
  cause buffer overflow
*
  Makefile dependencies are wrong, which cause problems during parallel build
*
  Unsigned overflow in ``udelay()``, which causes sleep to be shorter than
  expected
*
  The CR0 intercept handler is wrong
*
  WRMSR intercept ignores ``vmx_msr_area_msrs``, leading to unexpected values
  read by the guest
*
  Guest x2APIC not blocked, so guest may be able to send INIT to a CPU
*
  Incorrect assert in hpt.c for long mode paging (but should be unused)
*
  NMI quiesce handling is wrong, can cause deadlock and lose guest NMIs
*
  ``HALT()`` does not halt forever, which cause troubles during debugging
*
  Last entry of E820 is dropped
*
  Guest CR4.VMXE should not be set, but is set
*
  Incorrect logic in booting, which cause problems for single CPU machines
*
  Guest initial state does not follow spec (e.g. DX, CR0, ...)
*
  ``_vmx_int15_handleintercept()`` does not truncate RSP
*
  Incorrect default MTRR is assumed, causing strange cache errors in Windows 10
*
  Did not block guest's MTRR changes, so guest can change host's memory cache
  settings
*
  Did not block microcode update, so guest can update microcode arbitrarily
*
  VGA driver references NULL pointer (problem only in debugging)
*
  ``xmhf_xcphandler_idt_start()`` incorrectly uses .fill, causing less area for
  IDT than expected
*
  Two unused nmm function may have a bug

