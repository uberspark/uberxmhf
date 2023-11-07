.. include:: /macros.rst


Hardware Requirements
=====================

Real hardware
-------------

* An **Intel** CPU (AMD is not supported)

  * Note: CPUs newer than Haswell have not been tested yet

* **A TPM (v1.2)** The BIOS feature is often called something like "embedded security device"

* **Hardware Virtualization extensions**

  * **Intel**\ : Virtualization Technology (VT-x)

* **Hardware Support for DMA Isolation**

  * **Intel**\ : Virtualization Technology for Directed I/O (VT-d)

* **2nd-level page tables** Typically turned on implicitly along with Virtualization extensions, if the processor supports it.

  * **Intel**\ : Extended Page Tables (EPT)

* **Dynamic root of trust**

  * **Intel**\ : Trusted Execution Technology (TXT). This feature is implemented partially by a signed software 
    module, called an SINIT module. Some processors exist that have the TXT hardware support but do not (yet) have 
    an SINIT module. Look for the SINIT module here: http://software.intel.com/en-us/articles/intel-trusted-execution-technology/

..  note::
    When purchasing a new machine, do *not* take it for granted that any
    newer Intel processor will have the necessary capabilities.

    * Check Intel processor capabilities: http://ark.intel.com/

Hypervisor
----------

Running uberXMHF in a hypervisor helps debugging. However, some features are
not available.

*
  QEMU / KVM: supported for Intel CPU, require ``--enable-kvm`` and ``vmx``
  flag in the CPU. Does not support DRT and DMAP.
*
  VMWare: probably supported.

