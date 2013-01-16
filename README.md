Introduction
============

XMHF is a modular hypervisor platform for recent multicore x86
hardware with support for dynamic root of trust and nested
(2-dimensional) paging.  It is NOT a full virtual machine monitor.

XMHF takes a developer-centric approach to hypervisor design and
implementation, and strives to be a comprehensible and flexible
platform for performing hypervisor research and development. XMHF
encapsulates common hypervisor core functionality in a framework that
allows others to build custom hypervisor-based solutions (called
"hypapps"). It currently supports only a single "rich" guest OS.

Included modules
================

The XMHF project includes several components:

* [XMHF](xmhf): The eXtensible Hypervisor Framework.

* [TrustVisor](trustvisor): A special-purpose hypervisor that provides
  code integrity as well as data integrity and secrecy for userspace
  Pieces of Application Logic (PALs).

    * [tee-sdk](tee-sdk): The Trusted Execution Environment Software
      Development Kit. This is a set of tools and APIs for developing
      PALs and applications that use them.

    * [tee-cred](tee-cred): The TEE Credential Manager (tee-cred) is
      an audited key-value store that is useful as a credential (e.g.,
      password) manager.  It is implemented in a PAL leveraging
      tee-sdk, and as a stand-alone audit server.

* [Lockdown](lockdown): Lockdown provides the user with a red/green
  system: an isolated and constrained environment for performing
  online transactions, as well as a high-performance, general-purpose
  environment for all other (non-security-sensitive) applications. An
  external device verifies which environment is active and allows the
  user to securely learn which environment is active and to switch
  between them.

* [libbaremetal](libbaremetal): Utility functions used across modules,
  including many utility function from libc, error-handling, logging,
  etc.  As the name implies, this library is intended primarily for
  use in "bare metal" environments.

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

Related Publications
====================

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
  [pdf](https://sparrow.ece.cmu.edu/group/pub/lockdown.pdf)

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

