Introduction
============

TrustVisor is a special-purpose hypervisor that provides measured, 
isolated execution environments for security-sensitive
code modules (Pieces of Application Logic - PALs) 
without trusting the OS or the application that invokes the code modules.

The isolated execution environment protects the code
integrity, execution integrity, as well as data integrity and secrecy
for PALs. TrustVisor produces evidence of
its initialization in the TPM's Platform Configuration Registers.
This evidence (in the form of a hash chain) can be used to generate a
TPM-based attestation that TrustVisor has loaded on a platform.
Further, TrustVisor implements a software-based, “micro-TPM” (µTPM) 
that can execute at higher speed on the platform’s primary CPU than
hardware TPM. It also generates and manages its own identity keypair
that can be used to generate subsequent attestations to the isolation
and execution of individual PALs, leveraging the µTPM.

The implementation of TrustVisor contained herein leverages [XMHF](../../xmhf).  
The original design and implementation of TrustVisor is described in:

*TrustVisor: Efficient TCB Reduction and Attestation*. Jonathan
M. McCune, Yanlin Li, Ning Qu, Zongwei Zhou, Anupam Datta, Virgil
Gligor, and Adrian Perrig. IEEE Symposium on Security and Privacy, May
2010. [pdf](http://www.ece.cmu.edu/~jmmccune/papers/MLQZDGP2010.pdf)

Documentation
=============

* [Building TrustVisor](doc/building-trustvisor.md)
* [Installing TrustVisor](doc/installing-trustvisor.md)


Software Development Kit (TEE-SDK)
==================================

TrustVisor is released with a Trusted-Execution-Environment Software-Development-Kit
(TEE-SDK), which comprises tools and documentation for developing
PALs and integrating them to applications. Please install [TEE-SDK](tee-sdk) and
try out some TrustVisor-specific PAL examples at 'tee-sdk/examples'. Note that
the APIs provided in TEE-SDK are intended to provide sufficient abstraction
such that PALs and applications can be ported to use alternative trusted 
environments, other than TrustVisor, with little or no modification.


DISCLAIMER
==========

TrustVisor is a research prototype. The implementation does not yet fully
provide the security properties of the design. There are a number of
[KNOWN
VULNERABILITIES](https://sourceforge.net/p/xmhf/tickets/search/?q=_vulnerability%3ATrue),
and probably other unknown vulnerabilities.

You will likely experience full system
crashes with the risk of data loss for the guest OS. In particular,
there are a number of [KNOWN STABILITY
ISSUES](https://sourceforge.net/p/xmhf/tickets/search/?q=_instability%3ATrue).


