One of the main design goals of [XMHF](..) is to achieve automated verification
while coping with implementation changes as a result of development.
The [XMHF](..) core provides functionality common to many hypervisor-based 
security architectures and supports hypapps that augment the core with
additional security or functional properties while preserving the 
fundamental hypervisor security property of memory integrity 
(i.e., ensuring that the hypervisor’s memory is not modified by 
software running at a lower privilege level).

We have verified the memory integrity of the [XMHF](..) core
using a combination of automated and manual techniques.
The model checker [CBMC](http://www.cprover.org/cbmc) is employed for 
automatic verification.
Manual audits apply to a small portion of the code which we anticipate 
to remain mostly unchanged as
development proceeds. The manual audits include constructs
that CBMC cannot verify, including loops that iterate over
entire page tables, platform hardware initialization and interaction,
and concurrent threads coordinating multiple CPUs during initialization
that are challenging for current model-checkers. For more details
please refer to our 2013 IEEE Security and Privacy [paper](http://hypcode.org/paper-xmhf-IEEES&P-2013.pdf).

Verification Environment and Tools
==================================

OS: Ubuntu 10.10, 32-bit; Available [here](http://old-releases.ubuntu.com/releases/maverick/ubuntu-10.10-desktop-i386.iso)

Verification Tools: 
CBMC: v4.1 32-bit; Available [here](http://www.cprover.org/cbmc/download/cbmc_4.1_i386.deb)

Install using: 

	sudo dpkg -i cbmc_4.1_i386.deb

How do I verify XMHF and/or a hypapp?
=====================================

Configure and build XMHF/hypapp as described in the [Building XMHF](./building-xmhf.md)
section. The following describe the specific steps to verify the 
XMHF core memory integrity using the example verify hypapp.

Checkout the XMHF project source tree.

    cd $WORK
    git clone git://git.code.sf.net/p/xmhf/xmhf xmhf

Change working directory to the XMHF source tree root.

    cd $WORK/xmhf/xmhf

Generate the `./configure` script.

    ./autogen.sh

Configure the XMHF verify hypapp.

    ./configure --with-approot=src/example-hypapps/verify --with-apparchive=xmhfapp-verify.a

Verify
	
	make verify-all
	or
	make verify
	
make verify-all will perform full verification of the XMHF core
as well as the hypapp. Subsequently, you can use make verify to 
verify the hypapp assuming there are no further changes to the 
XMHF core.

Note that we assume CBMC is sound. i.e., if CBMC
reports a successful verification, then XMHF/hypapp preserve 
memory integrity.

For verification purposes, we also assume that a hypapp built on top 
of XMHF uses the prescribed XMHF core APIs and that it does not write to arbitrary
code and data. In fact, these are the only assumptions
required of any new hypapp to ensure the memory integrity
property of XMHF. In the current XMHF implementation, a single 
XMHF core API function xmhf_memprot_setprot
allows manipulating guest memory protections
via the HPTs. 





