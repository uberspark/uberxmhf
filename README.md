Introduction
============

The Uber eXtensible Micro-Hypervisor Framework (UberXMHF)
strives to be a comprehensive and flexible platform for performing 
hypervisor research and development. The framework facilitates 
design and development of custom (security-sensitive) hypervisor-enabled 
applications (called "uberapps").

UberXMHF is designed to achieve three goals: modular extensibility,
automated (compositional) verification, and high performance. 
UberXMHF includes a core that provides functionality common to many 
hypervisor-based security architectures and supports extensions that 
augment the core with additional security or functional properties while 
preserving the fundamental hypervisor security property of memory integrity 
(i.e., ensuring that the hypervisor's memory is not modified by 
software running at a lower privilege level).

UberXMHF advocates a "rich" commodity single-guest execution model 
(uberguest) where the hypervisor framework supports only a single, 
commodity guest OS and allows the guest direct access to all 
performance-critical system devices and device interrupts. 
In principle, the uberguest could also be a traditional hypervisor/VMM. 

UberXMHF currently runs on both x86 (Intel and AMD) and ARM (Raspberry PI) 
multi-core hardware virtualized platforms with support for 
nested (2-dimensional) paging. 
The framework is capable of running unmodified legacy multiprocessor 
capable OSes such as Windows and Linux.  

Hardware Platforms and Capabilities
===================================


| Platform 	| Verification Status 	| uberguests Tested	| Documentation |
| --- 		| 	--- 				| 			--- 	| --- 			| 
| x86-32 Intel PC |	Verified			| Ubuntu 12.04 LTS  (3.2.0-23-generic) |  [./uxmhf/README.md](uxmhf/README.md) |
| Raspberry PI 3 |	Planned			| Raspbian (4.4.y), <br> Emlid RT Linux (4.4.y) |  [./uxmhf-rpi3/README.md](uxmhf-rpi3/README.md) |
| x86-32 AMD PC, <br> x86-32 Intel PC (legacy) |	Verified			| Windows XP, <br> Ubuntu 12.04 LTS (3.2.0-23-generic) |  [./xmhf/README.md](xmhf/README.md) |




