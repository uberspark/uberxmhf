One of the design goals of XMHF is to achieve automated verification.
The XMHF core provides functionality common to many hypervisor-based 
security architectures and supports hypapps that augment the core with
additional security or functional properties while preserving the 
fundamental hypervisor security property of memory integrity 
(i.e., ensuring that the hypervisor’s memory is not modified by 
software running at a lower privilege level).

Verification Environment and Tools
==================================

Ubuntu 10.10, 32-bit, CBMC 4.1 32-bit

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





