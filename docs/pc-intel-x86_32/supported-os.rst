.. include:: /macros.rst


Supported OS
============

In principle, any guest operating system should be supported so 
long as it:

* Uses 'normal' 32-bit page tables. ** PAE is not supported **

The actively supported OS/distribution is:

* Ubuntu 16.04.x LTS with Linux Kernel 4.4.x (#CONFIG_X86_PAE is not set) and below with GRUB v0.97 (default version that
  ships with Ubuntu 16.04.x LTS)

The following guest OSes are also known to work:

* Ubuntu 12.04 LTS with Linux Kernel 3.2.0-27-generic and below
* Windows XP

..  note::
    Currently certain kernel modules must be black-listed (e.g., in ``/etc/modprobe.d/blacklist.conf``):
    
      * ``kvm``
      * ``kvm_intel``
      * ``intel_rapl``
