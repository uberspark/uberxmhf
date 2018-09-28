# uber eXtensible Micro-Hypervisor Framework (uberXMHF)

## Changelog

* Version 4.0 (Brawn)
	* first stand-alone uberXMHF release
	* added Raspberry PI 3 hardware platform support
	* consolidated past XMHF x86-32 AMD PC and x86-32 Intel PC (legacy) releases
	* various documentation updates

* Version 3.1 (Flak)
	* fixed uxmhf build errors

* Version 3.0 (Ratchet)
	* added support for Frama-C Phosphorus-20170501
	* added support for Compcert 3.0.1
	* fixed error due to improper inclusion of xh_ssteptrace in the verification process
	* minor build harness fixes and documentation updates

* Version 2.0 (Blades)
	* separated uberspark, uberspark libraries and uxmhf verification/build processes
	* refined and streamlined uberspark and uxmhf verification/build harness
	* fixed minor errors in documentation and updates to reflect release changes

* Version 1.0 (Cliff Jumper)
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
  