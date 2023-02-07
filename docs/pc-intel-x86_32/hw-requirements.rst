.. include:: /macros.rst


Hardware Requirements
=====================

* **A TPM (v1.2 or above)** The BIOS feature is often called something like "embedded security device"

* **Hardware Virtualization extensions**

  * Intel Virtualization Technology (VT-x)

* **Hardware Support for DMA Isolation**

  * Intel Virtualization Technology for Directed I/O (VT-d)

* **2nd-level page tables** Typically turned on implicitly along with Virtualization extensions, if the processor supports it.
  
  * Intel Extended Page Tables (EPT)

* **Dynamic root of trust**
  
  * Intel Trusted Execution Technology (TXT). 

..  note:: 
    When purchasing a new machine, do *not* take it for granted that any
    newer Intel will have the necessary capabilities. Check Intel processor 
    capabilities at: http://ark.intel.com/
