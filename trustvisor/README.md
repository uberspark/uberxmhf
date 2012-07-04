Introduction
============

TrustVisor is a special-purpose hypervisor that provides code
integrity as well as data integrity and secrecy for userspace Pieces
of Application Logic (PALs). The implementation of TrustVisor
contained herein leverages [XMHF](../xmhf).  TrustVisor produces evidence of
its initialization in the TPM's Platform Configuration Registers.
This evidence (in the form of a hash chain) can be used to generate a
TPM-based attestation that TrustVisor has loaded on a platform.
Further, TrustVisor generates and manages its own identity keypair
that can be used to generate subsequent attestations to the isolation
and execution of individual PALs.

The original design and implementation of TrustVisor is described in:

*TrustVisor: Efficient TCB Reduction and Attestation*. Jonathan
M. McCune, Yanlin Li, Ning Qu, Zongwei Zhou, Anupam Datta, Virgil
Gligor, and Adrian Perrig. IEEE Symposium on Security and Privacy, May
2010. [pdf](http://www.ece.cmu.edu/~jmmccune/papers/MLQZDGP2010.pdf)

DISCLAIMER
==========

TrustVisor is a ***research prototype***.

***TrustVisor is not secure***. The implementation does not yet fully
provide the security properties of the design. There are a number of
[KNOWN
VULNERABILITIES](https://sourceforge.net/p/xmhf/tickets/search/?q=_vulnerability%3ATrue),
and probably many more unknown vulnerabilities.

***TrustVisor is not stable***. You will likely experience full system
crashes with the risk of data loss for the guest OS. In particular,
there are a number of [KNOWN STABILITY
ISSUES](https://sourceforge.net/p/xmhf/tickets/search/?q=_instability%3ATrue).

Documentation
=============

* [Building TrustVisor](doc/building-trustvisor.md)
* [Installing TrustVisor](doc/installing-trustvisor.md)
* [NV Storage for TrustVisor](doc/nv-storage.md)

Design Concepts
===============

* [Sealing and Attestation](doc/sealing-attestation.md)
