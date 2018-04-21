# uber eXtensible Micro-Hypervisor Framework (uberXMHF)

## Introduction

The Uber eXtensible Micro-Hypervisor Framework (UberXMHF)
strives to be a comprehensive and flexible platform for performing 
hypervisor research and development. The framework facilitates 
design and development of custom (security-sensitive) hypervisor-enabled 
applications (called "uberapps").

UberXMHF is designed to achieve three goals: modular extensibility,
automated (compositional) verification, and high performance. 
UberXMHF includes a core that provides functionality common to many 
hypervisor-based security architectures and supports extensions that 
augment the core with additional security or functional properties while 
preserving the fundamental hypervisor security property of memory integrity 
(i.e., ensuring that the hypervisor's memory is not modified by 
software running at a lower privilege level).

UberXMHF advocates a "rich" commodity single-guest execution model 
(uberguest) where the hypervisor framework supports only a single, 
commodity guest OS and allows the guest direct access to all 
performance-critical system devices and device interrupts. 
In principle, the uberguest could also be a traditional hypervisor/VMM. 

UberXMHF currently runs on both x86 (Intel and AMD) and ARM (Raspberry PI) 
multi-core hardware virtualized platforms with support for 
nested (2-dimensional) paging. 
The framework is capable of running unmodified legacy multiprocessor 
capable OSes such as Windows and Linux.  

## Hardware Platforms and Capabilities


| Platform 	| Verification Status 	| uberguests Tested	| Documentation |
| --- 		| 	--- 				| 			--- 	| --- 			| 
| x86-32 Intel PC |	Verified			| Ubuntu 12.04 LTS  (3.2.0-23-generic) |  [./uxmhf/README.md](uxmhf/README.md) |
| Raspberry PI 3 |	Planned			| Raspbian (4.4.y), <br> Emlid RT Linux (4.4.y) |  [./uxmhf-rpi3/README.md](uxmhf-rpi3/README.md) |
| x86-32 AMD PC, <br> x86-32 Intel PC (legacy) |	Verified			| Windows XP, <br> Ubuntu 12.04 LTS (3.2.0-23-generic) |  [./xmhf/README.md](xmhf/README.md) |


## Contacts, Maintainers and Contributors
* Amit Vasudevan [amitvasudevan@acm.org] for uberXMHF: x86-32 Intel PC, Raspberry PI 3,
x86-32 AMD PC, x86-32 Intel PC (legacy), libbaremetal and Lockdown

* Zongwei Zhou for (TrustVisor and tee-sdk)

* Other contributors: Jonathan McCune, James Newsome, Ning Qu, and Yanlin Li


## Contributing

uberXMHF is always open to contributions. The easiest mechanism is probably to
fork the git repository through the web UI, make the changes on your fork, 
and then issue a pull request through the web UI.


## Copying

The uberXMHF project comprises code from multiple sources, under multiple
open source licenses. See [COPYING.md](COPYING.md) for details.

## Related Publications

* Have your PI and Eat it Too: Practical Security on a Low-cost Ubiquitous 
Computing Platform. Amit Vasudevan, Sagar Chaki. IEEE Euro Symposium on
Security and Privacy, 2018.

* UberSpark: Enforcing Verifiable Object Abstractions for Automated Compositional Security Analysis of a Hypervisor. Amit Vasudevan, Sagar Chaki, Petros Maniatis, Limin Jia, Anupam Datta. USENIX Security Symposium, 2016. [[pdf](http://hypcode.org/paper-uberspark-xmhf-USENIXSEC-2016.pdf)]

* UberSpark: Enforcing Verifiable Object Abstractions for Automated Compositional Security Analysis of a Hypervisor. Amit Vasudevan, Sagar Chaki, Petros Maniatis, Limin Jia, Anupam Datta. CMU CyLab Technical Report CMU-CyLab-16-003. June 2016. [[pdf](http://hypcode.org/tr_CMUCyLab16003.pdf)]

* Design, Implementation and Verification of an eXtensible and 
  Modular Hypervisor Framework. Amit Vasudevan, Sagar Chaki, Limin Jia,
  Jonathan M. McCune, James Newsome, and Anupam Datta. 
  IEEE Symposium on Security and Privacy, 
  May 2013. [pdf](http://hypcode.org/paper-xmhf-IEEES&P-2013.pdf)

* Building Verifiable Trusted Path on Commodity x86 Computers.
  Zongwei Zhou, Virgil Gligor, James Newsome, and Jonathan M. McCune. 
  IEEE Symposium on Security and Privacy (IEEE S&P), 2012.
  [pdf](http://users.ece.cmu.edu/~zongweiz/media/TP_Oakland12.pdf)

* "It's an app. It's a hypervisor. It's a hypapp.": Design and
  Implementation of an eXtensible and Modular Hypervisor
  Framework. Amit Vasudevan, Jonathan M. McCune, and James
  Newsome. Technical Report CMU-CyLab-12-014, June 2012.
  [pdf](http://www.cylab.cmu.edu/files/pdfs/tech_reports/CMUCyLab12014.pdf)

* TrustVisor: Efficient TCB Reduction and Attestation.  Jonathan
  M. McCune, Yanlin Li, Ning Qu, Zongwei Zhou, Anupam Datta, Virgil
  Gligor, and Adrian Perrig. IEEE Symposium on Security and Privacy,
  May 2010. [pdf](http://www.ece.cmu.edu/~jmmccune/papers/MLQZDGP2010.pdf)

* Lockdown: Towards a Safe and Practical Architecture for Security
  Applications on Commodity Platforms.  Amit Vasudevan and Bryan Parno
  and Ning Qu and Virgil D. Gligor and Adrian Perrig. Proceedings of
  the 5th International Conference on Trust and Trustworthy Computing
  (TRUST), June 2012.
  [pdf](http://hypcode.org/paper-lockdown-TRUST-2012.pdf)

* Lockdown: A Safe and Practical Environment for Security Applications
  (CMU-CyLab-09-011) Amit Vasudevan and Bryan Parno and Ning Qu and
  Virgil D. Gligor and Adrian Perrig. Technical Report
  CMU-CyLab-09-011, June 2009.
  [pdf](http://www.cylab.cmu.edu/files/pdfs/tech_reports/CMUCyLab09011.pdf)

  
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
  