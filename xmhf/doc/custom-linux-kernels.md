[XMHF](..) currently does not virtualize MTRRs (on Intel Platforms). On
Linux, you will need to build or obtain a kernel with MTRR
(`CONFIG_MTRR`) features disabled.

Get a 2.6.32.X version, in this case we used 2.6.32.46
 
When making a new kernel yourself, do:

* `make install`
   copies vmlinuz-2.6.32.46 into `/boot`
* `make modules_install`
   places modules in `/lib/modules/2.6.32.46`
* in `/boot`:
   mkinitramfs -o `initrd.img-2.6.32.46 2.6.32.46`
