# UberSpark: Enforcing Verifiable Object Abstractions for Automated Compositional Security Analysis of a Hypervisor

## Introduction
UberSpark (uSpark) is an innovative architecture for
compositional verification of security properties of extensible
hypervisors written in C and Assembly.

uSpark comprises two key ideas: 
(i) endowing low-level system software with abstractions found 
in higher-level languages (e.g., objects,
interfaces, function-call semantics for implementations of
interfaces, access control on interfaces, concurrency and
serialization), enforced using a combination of commodity
hardware mechanisms and light-weight static analysis; and
(ii) interfacing with platform hardware by programming
in Assembly using an idiomatic style (called CASM) that is
verifiable via tools aimed at C, while retaining its performance
and low-level access to hardware.

After verification, the C code is compiled using a
certified compiler while the CASM code is translated into its
corresponding Assembly instructions.
Collectively, these innovations
enable compositional verification of security invariants without
sacrificing performance.

We validate uSpark by building and verifying security invariants of an 
existing open-source commodity x86 micro-hypervisor, XMHF (available [here](http://xmhf.org))
and several of its extensions, and demonstrating only minor
performance overhead with low verification costs.

## Download
Below you will find our first (academic prototype) release of uSpark and uberXMHF (uXMHF)
-- code-named "cliff-jumper" -- as a gzipped-tarball. A github code repository is coming
soon! 

[UberSpark Release 1.0 ("cliff-jumper") ](http://hypcode.org/uberspark-1.0-cliff-jumper.tar.gz)

## Contact and Maintainer
Amit Vasudevan (amitvasudevan@acm.org)

## Related Publications

* UberSpark: Enforcing Verifiable Object Abstractions for Automated Compositional Security Analysis of a Hypervisor. Amit Vasudevan, Sagar Chaki, Petros Maniatis, Limin Jia, Anupam Datta. USENIX Security Symposium, 2016. [[pdf](http://hypcode.org/paper-uberspark-xmhf-USENIXSEC-2016.pdf)]

* UberSpark: Enforcing Verifiable Object Abstractions for Automated Compositional Security Analysis of a Hypervisor. Amit Vasudevan, Sagar Chaki, Petros Maniatis, Limin Jia, Anupam Datta. CMU CyLab Technical Report CMU-CyLab-16-003. June 2016. [[pdf](http://hypcode.org/tr_CMUCyLab16003.pdf)]


## Software requirements and dependencies
* Ubuntu 14.04 LTS 64-bit for development and verification (available [here](http://releases.ubuntu.com/14.04/))
* Compcert -- version 2.4 was used for the release (available [here](http://compcert.inria.fr/release/compcert-2.4.tgz))
* Frama-C -- version code-named "Sodium" was used for the release (available [here](http://frama-c.com/download_sodium.html)). You must also install CVC3, Alt-Ergo and Z3 as backend theorem provers. Take a look at the WP manual (available [here](http://frama-c.com/download/wp-manual-Sodium-20150201.pdf)) for more information on installing the theorem provers.
* gcc and binutils -- do a `sudo apt-get install gcc binutils` to install the latest versions

## Verfying and Building uberXMHF (uXMHF)

1. Unzip and untar the release sources within a directory
   
   `tar -xvzf uberspark-1.0-cliff-jumper.tar.gz`

2. Change directory to uberspark-1.0-(cliff-jumper)
   
   `cd uberspark-1.0-cliff-jumper`

3. Prepare for verification
   
    `autogen.sh`
   
    `./configure --prefix=/home/<home-dir>/<work-dir> --disable-debug-serial`
      
    `make verify_prep`

   replace `<home-dir>` with your home-directory name and `<work-dir>` with any working directory you choose.

4. Verifying individual uberobjects
   
   `cd xmhf-uobjs\<uobj-name>`
   
   `make verify`

   replace `<uobj-name>` with the uberobject directory name (e.g., `xh_hyperdep`)

5. Performing uberobject composition check

   `make verify_compcheck`

6. Verifying all the uberobjects

   `make verify_all`

7. Building the uberobject binaries and the final hypervisor image

    `./configure --prefix=/home/<home-dir>/<work-dir>`
      
    `make`

   replace `<home-dir>` with your home-directory name and `<work-dir>` with any working directory you choose. If everything goes well then a final hypervisor image `xmhf-x86-vmx-x86pc.bin.gz` will be generated.

## Installing uXMHF

Please see the hardware requirements of XMHF (available [here](http://xmhf.sourceforge.net/doc/xmhf/doc/hardware-requirements.md.html)) and the guest OSes supported (available [here](http://xmhf.sourceforge.net/doc/xmhf/doc/supported-OS.md.html)). More specifically, you will need an Intel TXT enabled chipset with EPT capabilities. The reference platform used for this release was a Dell Optiplex 9020 with an Intel Core-i5 4590 CPU running Ubuntu 12.04 LTS 32-bit SMP kernel  3.2.0-27-generic (note this is a non-PAE kernel).

Follow the installation instructions for XMHF (available [here](http://xmhf.sourceforge.net/doc/xmhf/doc/installing-xmhf.md.html)). However, replace the section on "GRUB entry to boot linux" with the following:

    `title uXMHF`
   
    `rootnoverify (hd0,1)                                      # should point to /boot`
   
    `kernel /xmhf-x86-vmx-x86pc.bin.gz serial=115200,8n1,0x3f8 # substitute in the correct serial address`
   
    `modulenounzip (hd0)+1                                     # should point to where grub is installed`
   
    `modulenounzip /4th_gen_i5_i7_SINIT_75.BIN                 # Intel TXT AC SINIT module`


##Debugging uXMHF

Refer to the debugging section in the original XMHF documentation (available [here](http://xmhf.sourceforge.net/doc/xmhf/doc/debugging-xmhf.md.html)).
