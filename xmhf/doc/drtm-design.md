DRTM Design
===========

Fundamental to XMHF's design is support for a ***measured launch***.
Presently we insist that it be a dynamic launch, on a platform that
supports Dynamic Root of Trust for Measurement (DRTM).  AMD and Intel
implement this differently, so we first point out some
platform-specific issues before discussing our design.

* First, mention significant requirements on each of AMD and Intel hardware platforms.
** AMD calls the launched environment an SLB.  Intel calls the launched environment an MLE.
** We call our secure loader the SL.
* Then, describe our SL design.

AMD
---

* Clear Microcode on all APs (and BSP) before attempting SKINIT
* SL(Secure Loader) must start on a 64K-aligned physical address
* SL starts in 32-bit flat protected mode.  Only CS and SS are valid.  EAX contains SL base address.  EDX contains some CPU information. ESP initialized to top of 64K.
* It is possible for launch to fail.  The SLB will still get control but PCR 17 will not hold the correct value.
    * TODO: Check for this failure and respond accordingly (retry launch).
* Upon entry into SLB, CS and SS are valid. DS is not.

Intel
-----

* [Intel MLE Developer's Guide](http://download.intel.com/technology/security/downloads/315168.pdf)
* [Intel SW Dev Guide Vol 2B, Ch. 6: Safer Mode Extensions](http://www.intel.com/Assets/PDF/manual/253667.pdf)


* TXT.* MSRs control aspects of DRTM
    * TXT.ERRORCODE, TXT.STS, TXT.ESTS, TXT.E2STS registers contain status information
    * In the event of a failed launch, TXT.ERRORCODE is our best chance of understanding what went wrong.
    * [tboot](http://tboot.sourceforge.net) contains some code to do this.  Indeed, it contains a lot of (BSD-licensed) code that we can leverage.
* We must be able to learn the start address and size of the SL from within init.
* We must be able to construct page tables that map the MLE so that Intel's Authenticated Code Module (ACMod, also known as SINIT) can address it properly.  In practice 3 4K pages should suffice.  These are PAE-formatted page tables.
* We must be able to access the appropriate SINIT module (start address and size) for the current chipset.
Initially I will hard-code this into x86/init for the HP 8540p laptops.
* This module will need to be copied to the physical addresses specified in some of the TXT MSR's; future systems may already include an SINIT module that was put in place by the BIOS.  I have yet to see one in the wild.
* No base address available in a register (AMD put it in EAX).  call/pop/align may be needed to learn base address.  However, newer systems will but the base of the MLE page tables into ECX.  We can determine if a system supports this by using GETSEC[CAPABILITIES].
* Upon entry into MLE, CS and DS are valid.  SS is not (opposite of AMD).  Can read memory with CS but must use DS to write.

Secure Loader Design / Implementation
=====================================

* SL header must somehow remain compatible with both AMD and Intel.
    * SL starts with 3 empty pages, except for the first 4 bytes.  These are initialized to contain the SLB header for an AMD system.  The entry point points beyond these three pages to the true entry point on the fourth page.  On an Intel system these three pages will be overwritten with the MLE page tables.  The MLE header will be written into the MLE at the beginning of the fourth page.
* To determine the SL's base addresses, the best cross-processor solution is to do:
    * `call 1f`
    * `1: pop eax`
    * This might introduce a problem if the default Intel stack pointer points into the runtime, where some important memory contents could be clobbered.  Likely work-around will be to manually set the stack pointer to 64K.  It will have to come after the type of processor is detected.  Again, I don't think this causes any trouble.
* Because writing memory can only be done with SS on AMD, and DS on Intel, we have to write differently depending on the processor.  This affects 3 locations in the code where the SL's GDT is dynamically updated.
* TODO: If GETSEC[CAPABILITIES] indicates that ECX will contain the MLE base address pointer upon entry into the MLE, we can use ECX as the base address on Intel systems.  This prevents errant memory writes from a not-entirely-understood SS on Intel.  Thus, we can scrap the call/pop/align and use EAX on AMD, and ECX on Intel.

Additional Intel-related issues
-------------------------------

* MTRRs must be set with caching disabled for SINIT to run, so system performance post-launch is poor.  These are currently restored in `runtime.c:allcpus_common_start()`.
    * NOTE: This may be too late to get good boot performance, since the SL runs (and builds page tables) without appropriate caching.
* Bringing APs online requires TXT-specific mechanisms.

TODOs
=====

* Block guest access to TPM localities > 1.
* Understand STM and use it
* Understand DMA protections and use them
