---
layout: page
tocref: uber eXtensible Micro-Hypervisor Framework Documentation &gt; pc-intel-x86_32 
title: Verifying and Building
---

## Software Requirements and Dependencies

UberSpark development and verification framework (available [here](http://uberspark.org)).


<br/>  
## Verfying

Execute the following, in order, within the `uxmhf/` folder in the root
tree of the sources:


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



<br/>  
## Building
 
Execute the following, in order, within the `uxmhf/` folder in the root
tree of the sources:
 
1.	Configure the serial debug output

	`./configure --enable-debug-serial=<your-serial-port-number>`

	replace `<your-serial-port-number>` with the system serial port number.
	Note: if you omit the parameter to `--enable-debug-serial` the default port chosen
	is `0x3f8` or `COM1`.

 
2.	Building the uberobject binaries and the final hypervisor image

      
	`make uxmhf-image`
	
	If everything goes well then a final hypervisor image `xmhf-x86-vmx-x86pc.bin.gz` will be generated.
 	