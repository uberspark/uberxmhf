.. include:: /macros.rst


Supported OS
============

In principle, any guest operating system should be supported so 
long as it:


* Uses 'normal' 32-bit page tables. ** PAE is not supported **

The following guest OSes are known to work:


* Ubuntu 16.04 LTS with Linux Kernel 4.4.x (#CONFIG_X86_PAE is not set) and below
* Ubuntu 12.04 LTS with Linux Kernel 3.2.0-27-generic and below

Note, that currently certain kernel modules must be black-listed (e.g., in `//etc/modprobe.d/blacklist.conf`):
`kvm`
`kvm_intel`
`intel_rapl`
