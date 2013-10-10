To *run* [TrustVisor](../) on a given machine, installation is the
same as for any other hypapp. See [Installing XMHF](../../../xmhf/doc/installing-xmhf.md).

On some platforms (e.g., HP EliteBook 2540p), if the TPM locality and non-volatile RAM
(NVRAM) are not properly configured, trustvisor crashes when attempting to access NVRAM
for its mater secret or to clear all TPM localities. An intrusive work-around is to restore 
the TPM to factory state via BIOS, and define NVRAM spaces in TPM, following the document 
[NV Storage for TrustVisor](nv-storage.md).
