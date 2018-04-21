# uberXMHF x86-32 Intel PC


## Software Requirements and Dependencies

UberSpark development and verification framework (available [here](http://uberspark.org)).


## Verfying and Building uberXMHF

Execute the following, in order, while in the top-level 
directory where this README.md resides:


1.	Prepare for verification
   
	`./bsconfigure.sh`
   
	`./configure --disable-debug-serial`
      
	`make uxmhf-verifyuobjs-prep`


2.	Verifying individual uberobjects
   
   	`cd xmhf-uobjs/<uobj-name>`
   
   	`make verify`

   	`cd ../..`

   	replace `<uobj-name>` with the uberobject directory name (e.g., `xh_hyperdep`)


3.	Performing uberobject composition check

   	`make uxmhf-verifyuobjs-compcheck`


4.	Verifying all the uberobjects

 	`make uxmhf-verifyuobjs-all`


5.	Building the uberobject binaries and the final hypervisor image

	`./configure`
      
	`make uxmhf-image`

   	If everything goes well then a final hypervisor image `xmhf-x86-vmx-x86pc.bin.gz` will be generated.


## Installing uberXMHF

You will need an Intel TXT enabled chipset with EPT capabilities. The reference platform used for this release was a Dell Optiplex 9020 with an Intel Core-i5 4590 CPU running Ubuntu 12.04 LTS 32-bit SMP kernel  3.2.0-23-generic (note this is a non-PAE kernel).

Follow the installation instructions for uberXMHF x86-32 Intel PC (legacy) (available [here](../xmhf/xmhf/doc/installing-xmhf.md)). However, replace the section on "GRUB entry to boot linux" with the following:

`title uXMHF`
   
`rootnoverify (hd0,1)                                      # should point to /boot`
   
`kernel /boot/xmhf-x86-vmx-x86pc.bin.gz serial=115200,8n1,0x3f8 # substitute in the correct serial address`
   
`modulenounzip (hd0)+1                                     # should point to where grub is installed`
   
`modulenounzip /boot/4th_gen_i5_i7_SINIT_75.BIN                 # Intel TXT AC SINIT module`

## Debugging uberXMHF

Refer to the debugging section for XMHF x86-32 Intel PC (legacy) (available [here](../xmhf/xmhf/doc/debugging-xmhf.md)).


