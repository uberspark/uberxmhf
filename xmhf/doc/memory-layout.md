Memory Layout and Integrity Checking Design (current as of 2012-07-03)
======================================================================

First, the memory layout of the Secure Loader (SL) and Runtime is summarized here.  This needs to remain consistent with the code.

Then, a strategy for computing hashes of various components during the build process is laid out.  These hashes are then used to do integrity checking (as well as sanity-checking, which gives hints that there may be a problem, but does not provide security properties).

Memory Layout
-------------

### Runtime ###

* This information extracted from the output of `objdump -h xmhf/src/xmhf-core/components/xmhf-runtime/runtime.exe`, see also `xmhf/src/xmhf-core/components/xmhf-runtime/runtime.lds.S`:

<pre>
Idx Name          Size      VMA               LMA               File off  Algn
  0 .text         00047000  00000000c0000000  00000000c0000000  00200000  2**5
                  CONTENTS, ALLOC, LOAD, READONLY, CODE
  1 .data         00422000  00000000c0047000  00000000c0047000  00247000  2**5
                  CONTENTS, ALLOC, LOAD, DATA
  2 .palign_data  05276000  00000000c0469000  00000000c0469000  00669000  2**5
                  CONTENTS, ALLOC, LOAD, DATA
  3 .stack        00014000  00000000c56df000  00000000c56df000  058df000  2**5
                  CONTENTS, ALLOC, LOAD, DATA
  4 .unaccounted  00000000  0000000000000000  0000000000000000  00200000  2**2
                  CONTENTS, ALLOC, LOAD, CODE
</pre>

* `.palign_data` is large, as it contains memory management data structures, but should be safe to measure ahead of time.
    * TODO: Make sure it is okay that the runtime's size may not be divisible by 2M, as SL rounds up many addresses to 2M
* The runtime's file is currently quite massive because it includes a giant set of page tables as part of its image.
    * TODO: Drastically shrink `.palign_data`, e.g., by generating it during bootup.

### Secure Loader (SL) ###

* This information extracted from the output of `objdump -h ./xmhf/src/xmhf-core/components/xmhf-sl/sl_syms.exe`, and can also be inferred from `xmhf/src/xmhf-core/components/xmhf-sl/sl.lds.S`:
<pre>
Idx Name          Size      VMA               LMA               File off  Algn
  0 .sl_header    00003000  0000000000000000  0000000000000000  00200000  2**12
                  CONTENTS, ALLOC, LOAD, DATA
  1 .text         00009245  0000000000003000  0000000000003000  00203000  2**4
                  CONTENTS, ALLOC, LOAD, READONLY, CODE
  2 .data         000000b8  000000000000c260  000000000000c260  0020c260  2**5
                  CONTENTS, ALLOC, LOAD, DATA
  3 .rodata       00002910  000000000000c320  000000000000c320  0020c320  2**5
                  CONTENTS, ALLOC, LOAD, READONLY, DATA
  4 .bss          000006d0  000000000000ec40  000000000000ec40  0020ec30  2**5
                  ALLOC
  5 .sl_stack     00000cf0  000000000000f310  000000000000ec30  0020ec30  2**0
                  CONTENTS, ALLOC, LOAD, READONLY, DATA
  6 .sl_untrusted_params 001f0000  0000000000010000  0000000000010000  00210000  2**5
                  CONTENTS, ALLOC, LOAD, DATA
  7 .unaccounted  00000000  0000000000000000  0000000000000000  00200000  2**2
                  CONTENTS, ALLOC, LOAD, CODE
</pre>

The first five sections (0-5) are trusted.  The linker enforces that they do not grow beyond 64 KB using a "MEMORY" region in `xmhf/src/xmhf-core/components/xmhf-sl/sl.lds.S`:

<pre>
MEMORY
{
  low  (rwxai) : ORIGIN = 0,   LENGTH = 64K
  high (rwxai) : ORIGIN = 64K, LENGTH = 1984K /* balance of 2M total */
  unaccounted (rwxai) : ORIGIN = 0, LENGTH = 0 /* see section .unaccounted at end */
}
</pre>

If too much code is added to the first 64K, it will produce a link error.

Only the first 64K are "trusted".  At 64K (0x10000), section `.sl_untrusted_params` begins, and this is untrusted input data for the SL.  The only expected content here at the moment (2012-07-03) is a single instance of `struct _sl_parameter_block` (defined in `xmhf/src/xmhf-core/include/xmhf-types.h`).

The SL must validate all input data in the `_sl_parameter_block`.  It is not measured.

* Observation: All sections are contiguous.  `.sl_untrusted_params` is largely empty.

Integrity Checking Strategy (hashes are trusted)
------------------------------------------------

During compilation, the Runtime is built first, the SL is built second, and INIT is built last.  There is no security-relevant reason that INIT has any dependency here, but I am currently using it to sanity check that things are decompressed and laid out in memory as one might expect.  I.e., INIT gets embedded in it expected hash values for the Runtime, and the Low 64K of the SL.  If any of the ASSERT()s or other checks fail in init, it likely means some assumption that this measurement process depends on has been violated.

### Measuring and Checking the Runtime ###

The runtime's hash is embedded inside the first 64K of the SL.  I (Jon) decided to do this using a preprocessor macro that can be passed in at build time, so that we do not depend on any auto-generated C files that would change with every compilation.  The expected ("golden") hash itself is computed from runtime.bin, before it is compressed, using sha1sum in `xmhf/src/xmhf-core/Makefile`:

<pre>
sl: runtime
    #EMHF secure loader component
    # Double-dollar-sign required to cause make to provide literal dollar sign to perl
    # Objective: Create an escaped ASCII string containing the SHA-1 hash of the
    # runtime and pass it to the SL's makefile
    cd components/xmhf-sl && $(MAKE) -w all \
            RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./components/xmhf-runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"
</pre>

This spits out an ASCII string that uses a bunch of escaped hex characters to encode a 20-byte binary literal.  The double-dollar-signs are escaping a single dollar sign from Make, and the double-backslahes are escaping a single backslash from the shell.  This sets a parameter RUNTIME_INTEGRITY_HASH to the value of the SHA-1 hash of the runtime binary image.  The SL's Makefile then uses this to populate a C preprocessor macro called ___RUNTIME_INTEGRITY_HASH___.  My intention is for the triple-underscore to indicate build-process-generated values.

`g_sl_gold` is then defined in `xmhf/src/xmhf-core/components/xmhf-sl/arch/x86/sl-x86.c`, which ends up containing the appropriate hash values, which can be used to compare the result of a SHA-1 computed over the entire runtime memory area during XMHF bootup.

When the make process descends into the SL, one sees console output like the following:

<pre>
cd components/xmhf-sl && make -w all \
		RUNTIME_INTEGRITY_HASH=\""\\x3d\\x57\\x4a\\x27\\xa0\\xec\\xd1\\x0c\\x27\\x23\\x2e\\x7d\\xea\\x98\\xd3\\x78\\x47\\xe5\\xe5\\xf8"\"
</pre>

This is the ASCII string containing the 20-byte SHA-1 hash of the runtime for commit a71a10ac52e43f8162de4e40cf7db60e9721a432.  You can get the same value via:

<pre>
$ sha1sum ./xmhf/src/xmhf-core/components/xmhf-runtime/runtime.bin
3d574a27a0ecd10c27232e7dea98d37847e5e5f8  ./xmhf/src/xmhf-core/components/xmhf-runtime/runtime.bin
</pre>

### Secure Loader ###

* The secure loader is measured by the CPU during creation of the Dynamic Root of Trust (i.e., SKINIT on AMD or GETSEC[SENTER] on Intel). See [DRTM Design](drtm-design.md).
* The first 64K of the secure loader (sections .sl_header, .text, .data, .bss, and .sl_stack) are measured implicitly during DRTM establishment.
    * Section `.sl_header` will contain different values depending on whether the CPU is AMD or Intel.
        * AMD: it will contain a 4-byte SLB header, and the remainder will be padding.
        * Intel: the first 3 pages (12K) will be the MLE page tables, and will not actually be part of the measured environment
    * Fallout from this is that the expected measurement of the SL will be different depending on whether it was measured by an Intel CPU or an AMD CPU.
        * TODO: Create a script that produces the expected PCR hash values at build time

Right now INIT computes an expected PCR-17 value for an AMD system.  This has been tested and found to be correct on the Dell PowerEdge T105, which is the only suitable AMD system I have at the moment.

Boot Messages
-------------

Here's an example of some serial debug output and how it relates:

### Security-critical (SL checks Runtime) ###

<pre>
SL: Golden Runtime SHA-1: 3d 57 4a 27 a0 ec d1 0c 27 23 2e 7d ea 98 d3 78
SL: Golden Runtime SHA-1: 47 e5 e5 f8
...
hashandprint: processing 0x056f3000 bytes at addr 0x00200000
SL: Computed Runtime SHA-1: : 3d 57 4a 27 a0 ec d1 0c 27 23 2e 7d ea 98 d3 78 47 e5 e5 f8
</pre>

The "Golden" SHA-1 is the one that was injected during the build process, as described above.  The "Computed" SHA-1 was literally computed by running SHA-1 over the runtime image in memory.  They match!

### Debug-useful ###

Init prints some expected values, and does some computations, though an adversary could cause them to be wrong.

Here's the runtime info, which is again consistent:
<pre>
INIT(early): *UNTRUSTED* gold runtime: 3d 57 4a 27 a0 ec d1 0c 27 23 2e 7d ea 98 d3 78
INIT(early): *UNTRUSTED* gold runtime: 47 e5 e5 f8
hashandprint: processing 0x056f3000 bytes at addr 0xb8200000
INIT(early): *UNTRUSTED* comp runtime: : 3d 57 4a 27 a0 ec d1 0c 27 23 2e 7d ea 98 d3 78 47 e5 e5 f8
</pre>

And here's the low 64K of the SL, which should actually end up in the TPM:

<pre>
INIT(early): *UNTRUSTED* gold SL low 64K: 8b 77 27 fb cf 5a 0a 7c 8a b8 a5 bf a5 52 bf 0d
INIT(early): *UNTRUSTED* gold SL low 64K: 9f 6f 45 0f
hashandprint: processing 0x00010000 bytes at addr 0xb8000000
INIT(early): *UNTRUSTED* comp SL low 64K: : 8b 77 27 fb cf 5a 0a 7c 8a b8 a5 bf a5 52 bf 0d 9f 6f 45 0f
</pre>

With this knowledge, you can compute the expected PCR-17 value for an AMD system. Its value is `SHA-1(SHA-1(0x0000000000000000000000000000000000000000)||SHA-1(SecureLoaderBlock))`.  Let's compute the SHA-1 hash of the low 64K of the SL:

<pre>
$ dd if=xmhf/src/xmhf-core/components/xmhf-sl/sl.bin bs=1024 count=64 | openssl dgst -sha1 -binary > /tmp/low64KofSL.bin
$ hd /tmp/low64KofSL.bin
8b 77 27 fb cf 5a 0a 7c  8a b8 a5 bf a5 52 bf 0d 9f 6f 45 0f
</pre>

It matches the value printed out above.  Good.  Now, let's re-create what should have happened to populate PCR-17:

<pre>
$ dd if=/dev/zero bs=1 count=20 > /tmp/20zeros.bin
$ cat /tmp/20zeros.bin /tmp/low64KofSL.bin | openssl dgst -sha1
d8d581d3893bef45ca1e503c64494348161e3420
</pre>

* TODO: It is desirable to add support to compute the expected PCR-17 value during boot, to ensure that SKINIT was successful and retry if necessary (resulting in better availability). See [tickets:#72].

You can check the PCR values by logging into the target system as root (assuming it runs Linux; there are also ways to read the PCRs on Windows).  Make sure the driver is loaded (`sudo modprobe tpm_tis` if it's not):

<pre>
$ lsmod | grep tpm
tpm_tis                 7294  1
tpm                    13452  1 tpm_tis
tpm_bios                5203  1 tpm
</pre>

Print the PCR value you care about:

<pre>
$ grep PCR-17 \`find /sys -name pcrs\`
PCR-17: D8 D5 81 D3 89 3B EF 45 CA 1E 50 3C 64 49 43 48 16 1E 34 20
</pre>

They match!


