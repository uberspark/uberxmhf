/* 
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 * 
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc
 *               http://xmhf.org
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of 
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

###################################################################
# WARNING WARNING WARNING WARNING WARNING WARNING WARNING WARNING #
###################################################################

You can ruin your motherboard on Intel hardware if your BIOS is
buggy. MAKE SURE YOUR BIOS IS UP TO DATE, and use the newest available
SINIT module from Intel:
http://software.intel.com/en-us/articles/intel-trusted-execution-technology/
If you want to be sure your hardware is working, we suggest starting
with Intel's tboot project: http://tboot.sourceforge.net/

================
= Introduction =
================

XMHF is a modular hypervisor platform for recent multicore x86
hardware with support for dynamic root of trust and nested
(2-dimensional) paging.  It is NOT a full virtual machine monitor.
The best place to get support and the most recent documentation is on
the XMHF web page: http://xmhf.org/

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

Two interesting hypapps are included: TrustVisor[1] and Lockdown[2,3].

libbaremetal
************

In keeping with our desire for small size and modularity, we break out
many basic utility functions that nearly any practical C program will
employ.


==============
= TrustVisor =
==============

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
*******

The Trusted Execution Environment Software Development Kit (tee-sdk)
is intended to make the life of a PAL developer significantly less
painful than it might otherwise be.  Example PALs leveraging tee-sdk
can be found in tee-sdk/trunk/examples/.

tee-cred
********

The TEE Credential Manager (tee-cred) is an audited key-value store
that is useful as a credential (e.g., password) manager.  It is
implemented in a PAL leveraging tee-sdk, and as a stand-alone audit
server.

============
= Lockdown =
============

Lockdown provides the user with a red/green system: an isolated and
constrained environment for performing online transactions, as well as
a high-performance, general-purpose environment for all other
(non-security-sensitive) applications. An external device verifies
which environment is active and allows the user to securely learn
which environment is active and to switch between them.

================
= KNOWN ISSUES =
================

Aesthetics and software engineering principles may have taken a back
seat to having running, working code before a deadline. We're trying
to incrementally improve the situation.

There are a substantial number of known technical issues with this
codebase, many of them with implications for security.  Please see the
issue tracker linked from http://xmhf.org/ for full details.  This
absolutely remains EXPERIMENTAL software.  If you trust your data to
this software, that is your problem.

=============
= CHANGELOG =
=============

xmhf-1.0: initial public release.

==============
= References =
==============

[1] TrustVisor: Efficient TCB Reduction and Attestation.  Jonathan
    M. McCune, Yanlin Li, Ning Qu, Zongwei Zhou, Anupam Datta, Virgil
    Gligor, and Adrian Perrig. IEEE Symposium on Security and Privacy,
    May 2010. http://www.ece.cmu.edu/~jmmccune/papers/MLQZDGP2010.pdf

[2] Lockdown: Towards a Safe and Practical Architecture for Security
    Applications on Commodity Platforms.  Amit Vasudevan and Bryan
    Parno and Ning Qu and Virgil D. Gligor and Adrian Perrig.
    Proceedings of the 5th International Conference on Trust and
    Trustworthy Computing (TRUST), June 2012.

[3] Lockdown: A Safe and Practical Environment for Security
    Applications (CMU-CyLab-09-011) Amit Vasudevan and Bryan Parno and
    Ning Qu and Virgil D. Gligor and Adrian Perrig. Technical Report
    CMU-CyLab-09-011, June 2009.
    http://www.cylab.cmu.edu/files/pdfs/tech_reports/CMUCyLab09011.pdf





