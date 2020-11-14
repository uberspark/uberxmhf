.. include:: /macros.rst


Adding hypapps
==============

Integrating a new uberapp into the micro-hypervisor requires the following integration pieces:

1. Create directory for hypapp functionality (e.g., `uapp_newapp`) within `uapps` directory
* `uapp-newapp.c` is used to perform the funcaitonality within a `bool uapp_newapp_handlehcall(uhcall_function, uhcall_buffer, uhcall_buffer_len)`
* Place header files in `include` as `newapp.h`. This header defines any data structures used for passing data, and a hypapp ID (`#define UAPP_NEWAPP_ACTION`)

2. To integrate the hypapp add references in the following locations:
* Add an `if(uapp_newapp_handlecall(r->r0, r->r1, r->r3))` to `core/ghcall.c`
* Add an entry to the `core/Makefile` (`uapp-newapp.o: ../uapps/uapp-newapp/uapp-newapp.c`), and add the `uapp-newapp.o` to the `core.bin:` line.

3. Add a test program that exercises your hypapp in `rgapps/linux`
* Create a directory for the test program (`rgapp-newapp`) that includes a `Makefile` and the testprogram (`rgapp-newapp.c`).
* In userspace, this test program will need to include `uhcall.h`, where the hypapp is called using `uhcall(UAPP_NEWAPP_ACTION, buf_ptr, sizeof(buf))`

4. Running userspace test programs.
* Load the kernel module (`uhcallkmod` in `rgapps/linux/rgapp-uhcallkmod`)
* Ensure the new device is read and writable from the calling applications (`chmod +x /dev/uhcallkmod`)
* Test program can now invoke hypapp
     

