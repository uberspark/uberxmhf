XMHF requires an enabled TPM to be enabled, as well as several advanced processor capabilities that typically need to be enabled in the BIOS. Unfortunately, every BIOS is different, so you may need to poke around a bit to find where these settings are located. They may also be called different things.

When purchasing a new machine, do *not* take it for granted that any newer Intel or AMD processor will have the necessary capabilities.

* Check Intel processor capabilities: http://ark.intel.com/
* Check AMD processor capabilities: http://www.amd.com/us/products/pages/processors.aspx (Look for AMD Virtualization™ (AMD-V™) Technology With Rapid Virtualization Indexing capability for the desired CPU model)

Requirement | AMD name | Intel name | comments
----------- | -------- | ---------- |
a TPM       |          |            | Often called something like 'embedded security device' in BIOS
Virtualization extensions | Secure Virtual Machine (SVM) or AMD Virtualization (AMD-V) | Virtualization Technology (VT-x)
2nd-level page tables     | Nested Page Tables (NPT) | Extended Page Tables (EPT) | Typically turned on implicitly along with Virtualization extensions, if the processor supports it
Dynamic root of trust     | Late-launch (default with AMD-V)   | Trusted Execution Technology (TXT) |
Has a published SINIT module | N/A | Check http://software.intel.com/en-us/articles/intel-trusted-execution-technology/ | Intel only. AMD does not require an SINIT module
