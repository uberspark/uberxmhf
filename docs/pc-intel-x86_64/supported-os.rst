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

Test matrix
-----------

We have tested XMHF + TrustVisor + pal_demo on the following configurations.

+-------+-----+-------------------+---------------+---------------------------+
|       |     |                   |               | Status                    |
|       |     |                   |               +-------+-------------------+
| XMHF  | DRT | Operating System  | Application   | HP    | QEMU              |
+=======+=====+===================+===============+=======+===================+
|  \*   | \*  | Ubuntu 12.04 i386 | pal_demo i386 | good  | good (no DRT)     |
+-------+     +-------------------+---------------+       |                   |
|  \*   |     | Debian 11 i386    | pal_demo i386 |       |                   |
+-------+     +-------------------+---------------+       |                   |
| amd64 |     | Debian 11 amd64   | pal_demo \*   |       |                   |
+-------+     +-------------------+---------------+       |                   |
| amd64 |     | Fedora 35 amd64   | pal_demo \*   |       |                   |
+-------+     +-------------------+---------------+       +-------------------+
|  \*   |     | WinXP i386 SP3    | pal_demo i386 |       | VMCALL workaround |
+-------+     +-------------------+---------------+       +-------------------+
| amd64 |     | WinXP amd64       | pal_demo \*   |       | good (no DRT)     |
+-------+     +-------------------+---------------+       |                   |
|  \*   |     | Win7 i386         | pal_demo i386 |       |                   |
+-------+     +-------------------+---------------+       |                   |
| amd64 |     | Win7 amd64        | pal_demo \*   |       |                   |
+-------+     +-------------------+---------------+       |                   |
| amd64 |     | Win8.1 amd64      | pal_demo \*   |       |                   |
+-------+     +-------------------+---------------+       |                   |
|  \*   |     | Win10 i386        | pal_demo i386 |       |                   |
+-------+     +-------------------+---------------+       +-------------------+
| amd64 |     | Win10 amd64       | pal_demo \*   |       | PAL not tested    |
+-------+-----+-------------------+---------------+-------+-------------------+

Column explanations

*
  XMHF: subarch of XMHF secureloader and runtime. amd64 for 64-bit, \* for
  32-bit and 64-bit.
*
  DRT: \* for both DRT enabled and DRT disabled. For QEMU only DRT disabled.
*
  Operating System: operating system and subarch.
*
  Application: the application run in XMHF (e.g. pal_demo for TrustVisor).

Test result explanations

*
  VMCALL workaround: Windows XP makes strange VMCALLs, which prevents
  TrustVisor from working correctly. To workaround the problem, the VMCALLs
  from Windows XP need to be ignored, and TrustVisor's VMCALL numbers need to
  be changed. After that, TrustVisor can run correctly.
*
  PAL not tested: Windows 10 amd64 is very slow when running in QEMU (due to
  slowness from nested virtualization). So this configuration is not tested.

