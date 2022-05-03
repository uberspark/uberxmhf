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

Compared to XMHF, XMHF-64 supports more guest operating system features, such
as PAE paging, 64-bit mode, x2APIC, MTRR change. It also supports later
compiler versions and can be compiled with optimization (e.g. GCC's ``-O3``).
Some bugs found in XMHF are fixed in XMHF-64. However, XMHF-64 is not formally
verified yet.

