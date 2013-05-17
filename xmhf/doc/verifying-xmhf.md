One of the design goals of XMHF is to achieve automated verification.
The XMHF core provides functionality common to many hypervisor-based 
security architectures and supports hypapps that augment the core with
additional security or functional properties while preserving the 
fundamental hypervisor security property of memory integrity 
(i.e., ensuring that the hypervisor’s memory is not modified by 
software running at a lower privilege level).

We have verified the memory integrity of the XMHF core
using a combination of automated and manual techniques.
The model checker CBMC(http://www.cprover.org/cbmc) is employed for 
automatic verification.
Manual audits apply to a small portion of the code which we anticipate 
to remain mostly unchanged as
development proceeds. The manual audits include constructs
that CBMC cannot verify, including loops that iterate over
entire page tables, platform hardware initialization and interaction,
and concurrent threads coordinating multiple CPUs during initialization
that are challenging for current model-checkers.

Verification Environment and Tools
==================================

OS: Ubuntu 10.10, 32-bit; Available here (http://old-releases.ubuntu.com/releases/maverick/ubuntu-10.10-desktop-i386.iso)

Verification Tools: 
CBMC: v4.1 32-bit; Available here (http://www.cprover.org/cbmc/download/cbmc_4.1_i386.deb)

Install using: 

	sudo dpkg -i cbmc_4.1_i386.deb

How do I verify XMHF and/or a hypapp?
=====================================

Configure and build the hypapp as described previously

make verify-all will perform full verification of the XMHF core
as well as the hypapp.

Subsequently you can use make verify to verify the hypapp assuming
there are no further changes to the XMHF core

note: verification is modulo the following assumptions: CBMC is
sound and hypapp needs to use prescribed core interfaces. Currently
xmhf_memprot_setprot is the core function which can be used to 
change memory protections of guest memory pages





