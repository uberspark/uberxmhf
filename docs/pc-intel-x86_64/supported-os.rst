.. include:: /macros.rst


Supported OS
============

In principle, any guest operating system should work, as long as it:

*
  Uses 32-bit paging / PAE paging / 4-level paging (5-level paging is not
  supported).
*
  Does not require hardware virtualization features, does not require TPM.
*
  Is stored in a MBR disk and booted by BIOS (GPT partition and EFI are not
  supported).

The following OS are known to work:

* Ubuntu 12.04 LTS
* Debian 11 with kernel 5.10.0-9
* Fedora 35
* Windows XP
* Windows 7
* Windows 8.1
* Windows 10
