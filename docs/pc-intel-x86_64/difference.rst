.. include:: /macros.rst

TODO: rename this rst file

Introduction
============

XMHF-64 is branch of XMHF that supports running XMHF in both 32-bit and 64-bit.
32-bit is called "i386" and 64-bit is called "amd64". This bit width difference
is called "subarch".

XMHF has 3 phases: bootloader, secureloader, and runtime. Bootloader will
always run in i386. Secureloader and runtime will run in the subarch as
configured by the user (i386 or amd64). Only amd64 XMHF can run amd64 guest
operating systems. A comparision is below.

===============  ============  =======================
Name             XMHF in i386  XMHF in amd64
===============  ============  =======================
bootloader       i386          i386
secureloader     i386          amd64
runtime          i386          amd64
guest OS         i386 (no PAE  i386 or amd64
physical memory  4 GiB         >= 4 GiB (configurable)
===============  ============  =======================

