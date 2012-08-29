XMHF requires an enabled TPM to be enabled, as well as several
advanced processor capabilities that typically need to be enabled in
the BIOS. Unfortunately, every BIOS is different, so you may need to
poke around a bit to find where these settings are located. They may
also be called different things.

When purchasing a new machine, do *not* take it for granted that any
newer Intel or AMD processor will have the necessary capabilities.

Check Intel processor capabilities: <http://ark.intel.com/>

Check AMD processor capabilities:
<http://www.amd.com/us/products/pages/processors.aspx>.
Look for AMD Virtualization (AMD-V) Technology With Rapid Virtualization
Indexing capability for the desired CPU model.

Requirements:

* **A TPM (v1.2)** The BIOS feature is often called something like
    "embedded security device"
* **Virtualization extensions**
    * **AMD**: Secure Virtual Machine (SVM) or AMD Virtualization (AMD-V)
    * **Intel**: Virtualization Technology (VT-x)
* **2nd-level page tables** Typically turned on implicitly along with
    Virtualization extensions, if the processor supports it.
    * **AMD**: Nested Page Tables (NPT)
    * **Intel**: Extended Page Tables (EPT)
* **Dynamic root of trust**
    * **AMD**: Late-launch (default with AMD-V)
    * **Intel**: Trusted Execution Technology (TXT). This feature is
        implemented partially by a signed software module, called an
        SINIT module. Some processors exist that have the TXT hardware
        support but do not (yet) have an SINIT module. Look for the
        SINIT module here:
        <http://software.intel.com/en-us/articles/intel-trusted-execution-technology/>
