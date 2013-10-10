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


Included modules
================

The XMHF project includes several components:

* [XMHF](xmhf): The eXtensible and Modular Hypervisor Framework 
  supporting custom hypervisor-based solutions (called "hypapps").

   * [libbaremetal](xmhf/src/libbaremetal): Utility functions used across modules,
     including many utility function from libc, error-handling, logging,
     etc.  As the name implies, this library is intended primarily for
     use in "bare metal" environments.

* [TrustVisor](hypapps/trustvisor): A special-purpose hypapp that provides
  code integrity as well as data integrity and secrecy for userspace
  Pieces of Application Logic (PALs).

    * [tee-sdk](hypapps/trustvisor/tee-sdk): The Trusted Execution Environment Software
      Development Kit. This is a set of tools and APIs for developing
      PALs and applications that use them.

* [Lockdown](hypapps/lockdown): A hypapp that provides the user with a red/green
  system: an isolated and constrained environment for performing
  online transactions, as well as a high-performance, general-purpose
  environment for all other (non-security-sensitive) applications. An
  external device verifies which environment is active and allows the
  user to securely learn which environment is active and to switch
  between them.

Copying
=======

The XMHF project comprises code from multiple sources, under multiple
open source licenses. See [COPYING.md](COPYING.md) for details.

Contact and support
===================

There are a substantial number of known technical issues with this
codebase, many of them with implications for security.  Please see the
[ticket tracker](https://sourceforge.net/p/xmhf/tickets/) for full
details. This absolutely remains EXPERIMENTAL software. Do not trust
important data to this software.

For bug reports, feature requests, etc., please use the sourceforge
[tickets](https://sourceforge.net/p/xmhf/tickets/) tool.

For other discussion and questions, please use the sourceforge
[discussion](https://sourceforge.net/p/xmhf/discussion/) tool. Note
that the discussion tool can also be used much like a traditional
mailing list, if you prefer. You will still need a sourceforge
account. You can subscribe to all messages or to individual message
threads through the web interface, after which you will receive
corresponding posts through email. You can also post by responding to
such notification messages, and start new threads by sending mail to
<general@discussion.xmhf.p.re.sf.net>. **Posts via email must
originate from a sourceforge account's primary email address**.

Contributing
============

We are open to contributions. The easiest mechanism is probably to
`fork` our [git repository](https://sourceforge.net/p/xmhf/xmhf/)
through the web UI, make the changes on your fork, and then issue a
`merge request` through the sourceforge web UI.

Contributors
============

The core team: Amit Vasudevan, Jonathan McCune, and James Newsome.

Current maintainer:
Amit Vasudevan (XMHF and Lockdown), Zongwei Zhou (Trustvisor)

Other contributors: Ning Qu (TrustVisor and Lockdown), 
and Yanlin Li (TrustVisor)


Related Publications
====================

* Design, Implementation and Verification of an eXtensible and 
  Modular Hypervisor Framework. Amit Vasudevan, Sagar Chaki, Limin Jia,
  Jonathan M. McCune, James Newsome, and Anupam Datta. 
  IEEE Symposium on Security and Privacy, 
  May 2013. [pdf](http://hypcode.org/paper-xmhf-IEEES&P-2013.pdf)

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
