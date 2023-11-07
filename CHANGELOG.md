# uber eXtensible Micro-Hypervisor Framework (uberXMHF)

## Changelog

* Version 6.2.0

	* Features
		* xmhf-64: initial commit, copied from xmhf
		* xmhf-64: fix compile errors found in high GCC version
		* xmhf-64: support running XMHF in 64-bit mode
		* xmhf-64: support continuous integration testing
		* xmhf-64: support running XMHF in QEMU
		* xmhf-64: support running XMHF with modern guest operating systems
		* xmhf-64: support running guests that use PAE paging
		* xmhf-64: provide ``pal_demo``, which compiles TrustVisor PALs in
		  Windows and Linux, without using linker scripts
		* xmhf-64: decrease compilation artifact size (e.g. object files)
		* xmhf-64: support optimized compile (e.g. ``-O3``)
		* xmhf-64: support DMAP in Intel
		* xmhf-64: allow the guest OS to change MTRR
		* xmhf-64: support x2APIC
		* xmhf-64: support Intel microcode update

	* Logic Fixes
		* xmhf-64: check `grube820list_numentries` in `dealwithE820()` to
		  prevent possible buffer overflow
		* xmhf-64: fix Makefile dependencies problems
		* xmhf-64: fix unsigned overflow in `udelay()`. This bug causes sleep
		  to be shorter than expected
		* xmhf-64: fix the CR0 intercept handler
		* xmhf-64: fix WRMSR intercept handler when MSR comes from
		  `vmx_msr_area_msrs`. This bug leads to unexpected values read by the
		  guest
		* xmhf-64: block guests' access to x2APIC. This bug may allow guests to
		  to send INIT to a CPU
		* xmhf-64: fix incorrect assert in hpt.c for long mode paging. This bug
		  is on a code path that is likely unused by 32-bit guests
		* xmhf-64: fix logic in NMI quiesce handling. This bug can cause
		  deadlock and lose of guest NMIs
		* xmhf-64: fix the problem that `HALT()` does not halt forever. This
		  bug can cause troubles during debugging
		* xmhf-64: fix the problem that the last entry of E820 is dropped
		* xmhf-64: unset CR4.VMXE, which is incorrectly set
		* xmhf-64: fix logic in booting, which causes problems for single CPU
		  machines
		* xmhf-64: fix guest initial state (e.g. DX, CR0, ...)
		* xmhf-64: truncate RSP in `_vmx_int15_handleintercept()`
		* xmhf-64: fix incorrect assumption about default MTRR type. This bug
		  causes strange cache errors in Windows 10
		* xmhf-64: block guests' change to MTRRs. This bug allows guests to
		  change host's memory cache settings
		* xmhf-64: block guest microcode update. This bug allows guests to
		  update microcode arbitrarily
		* xmhf-64: fix NULL pointer reference in the VGA driver. This bug is on
		  a code path that only happens when debugging
		* xmhf-64: fix incorrect use of .fill in `xmhf_xcphandler_idt_start()`.
		  This bug leads to less area allocated for IDT than expected
		* xmhf-64: remove two unused nmm functions that may contain bugs

* Version 6.1.0

	* Features
    	* uxmhf: add support for Intel 1st generation core CPU (HP 2540p laptop platform)

	* Documentation
    	* uxmhf: revise documentation to clarify OS and boot-loader support
		* uxmhf: clarify documentation on required OS kernel command line parameters and module blacklistings


* Version 6.0.0

	* Features
    	* uxmhf: add new üapp uhcalltest for testing hypercalls; add corresponding rich guest app for linux
    	* uxmhf: add configure option --with-debug-serial-maxcpus to specify platform cores while in debugging mode
	    * uxmhf: add support for non linear CPU id mappings setup by some BIOSes
    	* uxmhf-rpi3: add support for receive functionality (getc) within uart.h
    	* uxmhf-rpi3: add PL011 full UART uart_getc implementation
    	* uxmhf-rpi3: add support for PL011 full UART hardware flow control functionality
    	* uxmhf-rpi3: add support for mailboxes
    	* uxmhf-rpi3: add support for PL011 full UART based debugging
    	* uxmhf-rpi3/uapps: add new uberapp (stateDB) to track state entries updates (bounded by a max. value) via in-memory database.
    	* uxmhf-rpi3/uapps: add uapp-pvdriver-uart, a para-virtualized guest OS UART driver backend
    	* uxmhf-rpi3/uapps: add uapp-uagent, an uberapp that takes an input buffer and returns the encrypt/decrypt of the data based upon an AES secret key.
    	* uxmhf-rpi3/uapps: add new uapp (uhsign) for protected HMAC calculation
    	* uxmhf-rpi3/uapps: switch to using sha256 within uapp-uhsign
    	* uxmhf-rpi3/rgapps/linux - revise libuhcall and uhcallkmod  and migrate the va2pa function from user space to kernel driver. 
    	* uxmhf-rpi3/libs: add sha256 support within libxmhfcrypto
	    * uxmhf-rpi3/rgapps/linux/libs: add kernel library libkhcall for performing hypercall from OS kernel mode

	* Documentation
    	* revise top-level README with instructions on documentation build
    	* add software requirements within a top-level index toctree
    	* uxmhf: revise build and installation documentation to clarify grub and debug settings, kernel command line parameters, and modules that need to be blacklisted currently
		* uxmhf: revise instructions to add a new üapp and clarify OS kernel boot configuration details
    	* uxmhf: migrate documentation from markdown to restructured text syntax
		* uxmhf-rpi3: add information to turn on UART debugging and select mini/PL011 UART during build
    	* uxmhf-rpi3: add information to enable uhsign uberApp during build
		* uxmhf-rpi3: add information about different USB to serial cabling for miniuart and PL011 UART based debugging
		* uxmhf-rpi3: add documentation on how to enable and use uapp-uagent
		* uxmhf-rpi3: revise documentation on how to enable and use uapp-pvdriver-uart
    	* uxmhf-rpi3: add stateDB uberapp build documentation
    	* uxmhf-rpi3: add documentation to describe libuhcall (user-mode) and libkhcall (kernel-mode) hypercall libraries
    	* uxmhf-rpi3: revise instructions to configure existing üapps and add new üapps
    	* uxmhf-rpi3: clarify OS kernel boot configuration details
    	* uxmhf-rpi3: migrate documentation from markdown to restructured text syntax
    	* xmhf: migrate documentation from markdown to restructured text syntax

	* Fixes
		* uxmhf: revise xmhf-bootloader sources to cope with --disable-drt and --disable-dmap configure options
    	* uxmhf-rpi3: modify main.c to place uart_testrecv() inside a #ifdef to eliminate build errors if not configured for UART debugging

	* Build
    	* add sphinx based documentation build harness
    	* uxmhf-rpi3: revise build harness to include --enable-debug-uart, --enable-debug-uart-PL011, and --enable-uapp-uhsign configure options
    	* uxmhf-rpi3: autogenerate rpi3 config based on UART selection so we can enable/disable bluetooth UART accordingly
    	* uxmhf-rpi3: add docker container for building and installing uberXMHF on Raspberry Pi 3
    	* uxmhf-rpi3: rework build configuration options to decouple --enable-debug-uart and --enable-uart-{pl011,mini}

	* Others
    	* uxmhf-rpi3: clean up and use debug printf interface throughout
    	* uxmhf-rpi3: add function declarations to header files to remove warnings about implicit function declarations.
    	* uxmhf-rpi3: clean up some unused variables
    	* uxmhf-rpi3: use top-level uart.h to bring in UART backend interfaces (mini or PL011 UART)
    	* uxmhf-rpi3: move code whitelisting functionality into common/ (as it is used by uapp-uhsign and uapp-uagent).


* Version 5.0
	* various documentation fixes
	* rpi3-cortex_a53-armv8_32: refactored secure-boot, interrupt protection, 
	  DMA protection, and FIQ reflection as modular build-time options
	* rpi3-cortex_a53-armv8_32: fixed stability issues within core micro-hypervisor framework
	* pc-intel-x86_32: migrated debug and uobject info library to core uberspark framework
	* pc-intel-x86_32: migrated data types to be stdint compatible
	* pc-intel-x86_32: removed micro-hypervisor specific dependencies on uobject info table
	* pc-intel-x86_32: added new uobject uhmpgtbl to deal with hypervisor page tables for
	  unverified hypervisor uobjects
	* pc-intel-x86_32: added new uobject iotbl to deal with hypervisor legacy I/O tables 
	  for unverified hypervisor uobjects
	* pc-intel-x86_32: revised exhub uobject to handle IDT initialization and operation
	* pc-intel-x86_32: refactored build process to eliminate redundant passes

* Version 4.1
	* added support for Ubuntu 16.04 LTS with Linux kernel 4.4.x 32-bits (CONFIG_X86_PAE=n)
	* migrated uberobject manifests to JSON format
	* various documentation updates

* Version 4.0 
	* first stand-alone uberXMHF release
	* added Raspberry PI 3 hardware platform support
	* consolidated past XMHF x86-32 AMD PC and x86-32 Intel PC (legacy) releases
	* various documentation updates

* Version 3.1 
	* fixed uxmhf build errors

* Version 3.0 
	* added support for Frama-C Phosphorus-20170501
	* added support for Compcert 3.0.1
	* fixed error due to improper inclusion of xh_ssteptrace in the verification process
	* minor build harness fixes and documentation updates

* Version 2.0 
	* separated uberspark, uberspark libraries and uxmhf verification/build processes
	* refined and streamlined uberspark and uxmhf verification/build harness
	* fixed minor errors in documentation and updates to reflect release changes

* Version 1.0 
	* initial release of uberXMHF x86-32 Intel PC
  
* Version 0.2.2
    * various general documentation fixes and cleanup
    * tee-sdk: added patches for newlib and openssl libraries and removed deprecated/non-working examples 
    * re-organized framework components and revised configuration/build harness and related documentation	
    * fixed build errors with gcc 4.6.3
    * xmhf-core: re-factored verification harness and added support for 64-bit CBMC
  
* Version 0.2.1
	* tools: add scripts to deal with release tasks
	* xmhf-core: refactor runtime build harness
	* xmhf-core: add build debug information within generated binaries
	* xmhf-core: segregate Dynamic Root-of-Trust and DMA protection logic and build configuration options
	* xmhf-core: add support for upto 8 CPU cores 
	* xmhf-core: add XSETBV intercept handling on Intel platforms for CPUs with XSAVE capabilities 
	* xmhf-core: fix MTRR logic on Intel platforms to obtain required variable range MTRRs 
	* xmhf-core: fix issue related to physical/virtual address overlap for runtime 
  
* Version 0.2
	* xmhf-core: clarify documentation and add description for build configuration options and verification
	* xmhf-core: add build configuration options --with-target-platform and --with-target-arch to choose target platform and CPU arch.
	* xmhf-core: restructure core components and general cleanup
	* xmhf-core: add XMHF/hypapp verification harness for verifying core memory integrity
	* xmhf-core: fix build error with --enable-debug-vga configure option
  
* Version 0.1.2
    * xmhf-core: stability improvements - we can now handle guest NMIs gracefully
    * xmhf-core: stability improvements - we now support stock MTRR-enabled (linux) guest kernels on Intel platforms
    * test-bed fixes, refactoring and improvements - now supporting 3.2.0-27-generic (and below) with ubuntu
    * added documentation generator which takes in-tree markdown files and generates html output
    * fixed build target install-bin to include correct destination path
  
* Version 0.1.1
    * Added TPM performance profiling.
    * Stability improvements.
    * Intercept handling now serialized in the core.
    * XMHF now builds and runs on Ubuntu 12.04 (precise).
    * Replaced LGPL tlsf implementation with public domain implementation.
    * Added design-documents.
  
* Version 0.1 
   * Initial Release
  
