Introduction
============

XMHF is a modular hypervisor platform for recent multicore x86
hardware with support for dynamic root of trust and nested
(2-dimensional) paging.  It is NOT a full virtual machine monitor.
The best place to get support and the most recent documentation is on
the XMHF web page: <http://xmhf.org/>

XMHF takes a developer-centric approach to hypervisor design and
implementation, and strives to be a comprehensible and flexible
platform for performing hypervisor research and development. XMHF
encapsulates common hypervisor core functionality in a framework that
allows others to build custom hypervisor-based solutions (called
"hypapps").  It currently supports only a single "rich" guest OS
(currently tested with 32-bit non-PAE Linux, and 32-bit non-PAE
Windows XP and Windows Server 2003; MTRR support must be disabled on
Intel hardware, e.g., CONFIG_MTRR not set), and two "hyper-apps"
(hypapps): a primary and a secondary.

Two interesting hypapps are included: [TrustVisor](trustvisor) and
[Lockdown](lockdown).

libbaremetal
============

In keeping with our desire for small size and modularity, we break out
many basic utility functions that nearly any practical C program will
employ.


TrustVisor
==========

TrustVisor is a special-purpose hypervisor that provides code
integrity as well as data integrity and secrecy for userspace Pieces
of Application Logic (PALs). The implementation of TrustVisor
contained herein leverages XMHF.  TrustVisor produces evidence of its
initialization in the TPM's Platform Configuration Registers.  This
evidence (in the form of a hash chain) can be used to generate a
TPM-based attestation that TrustVisor has loaded on a platform.
Further, TrustVisor generates and manages its own identity keypair
that can be used to generate subsequent attestations to the isolation
and execution of individual PALs.

tee-sdk
-------

The Trusted Execution Environment Software Development Kit (tee-sdk)
is intended to make the life of a PAL developer significantly less
painful than it might otherwise be.  Example PALs leveraging tee-sdk
can be found in [tee-sdk/examples/](tee-sdk/examples/).

tee-cred
--------

The TEE Credential Manager (tee-cred) is an audited key-value store
that is useful as a credential (e.g., password) manager.  It is
implemented in a PAL leveraging tee-sdk, and as a stand-alone audit
server.

Lockdown
========

Lockdown provides the user with a red/green system: an isolated and
constrained environment for performing online transactions, as well as
a high-performance, general-purpose environment for all other
(non-security-sensitive) applications. An external device verifies
which environment is active and allows the user to securely learn
which environment is active and to switch between them.

KNOWN ISSUES
============

Aesthetics and software engineering principles may have taken a back
seat to having running, working code before a deadline. We're trying
to incrementally improve the situation.

There are a substantial number of known technical issues with this
codebase, many of them with implications for security.  Please see the
issue tracker linked from <http://xmhf.org/> for full details.  This
absolutely remains EXPERIMENTAL software.  If you trust your data to
this software, that is your problem.

CHANGELOG
=========

xmhf-1.0: initial public release.

References
==========

[1] TrustVisor: Efficient TCB Reduction and Attestation.  Jonathan
    M. McCune, Yanlin Li, Ning Qu, Zongwei Zhou, Anupam Datta, Virgil
    Gligor, and Adrian Perrig. IEEE Symposium on Security and Privacy,
    May 2010. <http://www.ece.cmu.edu/~jmmccune/papers/MLQZDGP2010.pdf>

[2] Lockdown: Towards a Safe and Practical Architecture for Security
    Applications on Commodity Platforms.  Amit Vasudevan and Bryan
    Parno and Ning Qu and Virgil D. Gligor and Adrian Perrig.
    Proceedings of the 5th International Conference on Trust and
    Trustworthy Computing (TRUST), June 2012.

[3] Lockdown: A Safe and Practical Environment for Security
    Applications (CMU-CyLab-09-011) Amit Vasudevan and Bryan Parno and
    Ning Qu and Virgil D. Gligor and Adrian Perrig. Technical Report
    CMU-CyLab-09-011, June 2009.
    <http://www.cylab.cmu.edu/files/pdfs/tech_reports/CMUCyLab09011.pdf>





