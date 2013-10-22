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

Documentation is automatically generated from markdown files in the 
code repository, and is viewable at http://xmhf.sourceforge.net/doc/


Changelog
=========

 * 0.1 Initial Release
 * 0.1.1
    * Added TPM performance profiling.
    * Stability improvements (ticket-28 fixed).
    * Intercept handling now serialized in the core.
    * XMHF now builds and runs on Ubuntu 12.04 (precise).
    * Replaced LGPL tlsf implementation with public domain implementation.
    * Added design-documents.
 * 0.1.2
    * xmhf-core: stability improvements (ticket-73 fixed) - we can now handle guest NMIs gracefully
    * xmhf-core: stability improvements (ticket-10 fixed) - we now support stock MTRR-enabled (linux) guest kernels on Intel platforms
    * test-bed fixes, refactoring and improvements - now supporting 3.2.0-27-generic (and below) with ubuntu
    * added documentation generator which takes in-tree markdown files and generates html output
    * fixed build target install-bin to include correct destination path
 * 0.2
	* xmhf-core: clarify documentation and add description for build configuration options and verification
	* xmhf-core: add build configuration options --with-target-platform and --with-target-arch to choose target platform and CPU arch.
	* xmhf-core: restructure core components and general cleanup
	* xmhf-core: add XMHF/hypapp verification harness for verifying core memory integrity
	* xmhf-core: fix build error with --enable-debug-vga configure option
 * 0.2.1
	* tools: add scripts to deal with release tasks
	* xmhf-core: refactor runtime build harness
	* xmhf-core: add build debug information within generated binaries
	* xmhf-core: segregate Dynamic Root-of-Trust and DMA protection logic and build configuration options
	* xmhf-core: add support for upto 8 CPU cores (ticket-74)
	* xmhf-core: add XSETBV intercept handling on Intel platforms for CPUs with XSAVE capabilities (ticket-74)
	* xmhf-core: fix MTRR logic on Intel platforms to obtain required variable range MTRRs (ticket-74)
	* xmhf-core: fix issue related to physical/virtual address overlap for runtime (ticket-31)
 * 0.2.2
    * various general documentation fixes and cleanup
    * tee-sdk: added patches for newlib and openssl libraries and removed deprecated/non-working examples 
    * re-organized framework components and revised configuration/build harness and related documentation	
	* fixed build errors with gcc 4.6.3
	* xmhf-core: re-factored verification harness and added support for 64-bit CBMC
	
