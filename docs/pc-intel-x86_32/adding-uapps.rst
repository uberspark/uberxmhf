.. include:: /macros.rst


Adding hypapps
==============

Integrating a new uberapp into the micro-hypervisor requires the following integration pieces:

1. Create directory for hypapp functionality (e.g., `xh_newapp`) within `xmhf-uobjs`
* `xh_newapp.gsm` defines key attributes of the hypapp.
* `xhnewapp_main.c` is used to invoke different operations (e.g., initialize, hypercall, shutdown, etc.). Where each of these opertions has a related file (`xhnewapp_hcbinit.c`)

2. To integrate the hypapp add references in the following locations:
* Add `xh_newapp` to the list in `xmhf-uobjs/UOBJLIST.in`
* Add a `DEFINE XMHFGEEC_SLAB_XH_NEWAPP` to `include/xmhf-config.h`
* Add a table entry to `static xc_hypapp_info_t _xcihub_hypapp_info_table[]` corresponding to the operations your hypapp performs in `xmhf-uobjs/include/xc.h`
* Add `xh_newapp` to the list of `uobj-callees` in `xmhf-uobjs/xc_init/sc_init.gsm` and `xmhf-uobj/xc_ihub/xc_ihub.gsm`

3. Ensure that your reconfigure prior to building (this is required to rewrite `xmhf-uobjs/UOBJLST` that is used by the `Makefile`).

4. Add a test program that exercises your hypapp in `xmhf-rgapps/linux`
* Create a directory for the test program (`rgapp-newapp`) that includes a `Makefile` and the testprogram (`rgapp-newapp.c`).
  * This test program will need to call `__vmcall(eax, ebx, edx, ecx)`, where `eax` is the hypercall ID, `ebx` is the high order 32-bit of the physical address, `edx` is the low-order 32-bit of the physical address (e.g., of an up to 4KB buffer being passed to the hypapp), and `ecx` is variable based upon the hypapp.



Note about naming conventions:
* xc = uberXMHF core
* xh = uberXMHF hypapps  
* xg = uberXMHF Guest
