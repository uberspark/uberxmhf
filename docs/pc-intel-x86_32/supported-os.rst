
----

layout: page
tocref: uber eXtensible Micro-Hypervisor Framework Documentation &gt; pc-intel-x86_32 

title: Supported OS
-------------------

In principle, any guest operating system should be supported so 
long as it:


* Uses 'normal' 32-bit page tables. ** PAE is not supported **

The following guest OSes are known to work:


* Ubuntu 16.04 LTS with Linux Kernel 4.4.x (CONFIG_X86_PAE=n) and below
* Ubuntu 12.04 LTS with Linux Kernel 3.2.0-27-generic and below
