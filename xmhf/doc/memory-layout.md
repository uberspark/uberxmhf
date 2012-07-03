h1. Memory Layout and Integrity Checking Design (current as of 2011-02-14)

First, the memory layout of the Secure Loader (SL) and Runtime is summarized here.  This needs to remain consistent with the code.

Then, a strategy for computing hashes of various components during the build process is laid out.  These hashes are then used to do integrity checking (as well as sanity-checking, which gives hints that there may be a problem, but does not provide security properties).

h2. Memory Layout

h3. Runtime

* This information extracted from the output of @objdump.exe -h emhfcore/x86/runtime/runtime_syms.exe@, see also emhfcore/runtime/runtime.lds.S
<pre>
Idx Name          Size      VMA               LMA               File off  Algn
  0 .text         00014000  00000000  00000000  00001000  2**4
                  CONTENTS, ALLOC, LOAD, READONLY, CODE, DATA
  1 .data         00008000  00014000  00014000  00015000  2**4
                  CONTENTS, ALLOC, LOAD, DATA
  2 .palign_data  04090000  0001c000  0001c000  0001d000  2**2
                  CONTENTS, ALLOC, LOAD, DATA
  3 .stack        00012000  040ac000  040ac000  040ad000  2**2
                  CONTENTS, ALLOC, LOAD, DATA
  4 .bss          00000010  040be000  040be000  00000000  2**4
                  ALLOC
</pre>

* .palign_data is large, contains global variables defined in emhfcore/x86/runtime/globals.c, but should be safe to measure ahead of time.
* XXX TODO Make sure it is okay that the runtime's size may not be divisible by 2M, as SL rounds up many addresses to 2M
* XXX Why is the runtime's file so massive?  TODO: Drastically shrink .palign_data, e.g., by generating it during bootup

h3. Secure Loader

* This information extracted from the output of @objdump.exe -h emhfcore/x86/sl/sl_syms.exe@, and can also be inferred from emhfcore/x86/sl/sl.lds.S:
<pre>
Idx Name          Size      VMA               LMA               File off  Algn
  0 .sl_header    00003000  00000000  00000000  00001000  2**2
                  CONTENTS, ALLOC, LOAD, DATA
  1 .text         00008000  00003000  00003000  00004000  2**4
                  CONTENTS, ALLOC, LOAD, READONLY, CODE
  2 .data         00001000  0000b000  0000b000  0000c000  2**4
                  CONTENTS, ALLOC, LOAD, DATA
  3 .bss          00001000  0000c000  0000c000  00000000  2**4
                  ALLOC
  4 .sl_stack     00003000  0000d000  0000d000  0000d000  2**2
                  CONTENTS, ALLOC, LOAD, DATA
  5 .sl_untrusted_params 001f0000  00010000  00010000  00010000  2**2
                  CONTENTS, ALLOC, LOAD, DATA
</pre>

The first five sections (0-4) are trusted.  The linker enforces that they do not grow beyond 64K using a "MEMORY" region in emhfcore/x86/sl/sl.lds.S:

<pre>
MEMORY
{
  low  (rwxai) : ORIGIN = 0,   LENGTH = 64K
  high (rwxai) : ORIGIN = 64K, LENGTH = 1984K /* balance of 2M total */ 
}
</pre>

If too much code is added to the first 64K, it will produce a link error.

Only the first 64K are "trusted".  At 64K (0x10000), section .sl_params begins, and this is untrusted input data for the SL.  The only expected content here at the moment (2011-02-14) is a single instance of struct _sl_parameter_block (defined in target.h).  

The SL must validate all input data in the _sl_parameter_block.  It is not measured.

* Observation: All sections are contiguous.  .sl_untrusted_params is largely empty.  

h2. Integrity Checking Strategy (hashes are trusted)

During compilation, the Runtime is built first, the SL is built second, and INIT is built last.  There is no security-relevant reason that INIT has any dependency here, but I am currently using it to sanity check that things are decompressed and laid out in memory as one might expect.  I.e., INIT gets embedded in it expected hash values for the Runtime, and the Low 64K of the SL.  If any of the ASSERT()s or other checks fail in init, it likely means some assumption that this measurement process depends on has been violated.

h3. Measuring and Checking the runtime.

The runtime's hash is embedded inside the first 64K of the SL.  I (Jon) decided to do this using a preprocessor macro that can be passed in at build time, so that we do not depend on any auto-generated C files that would change with every compilation.  The expected ("golden") hash itself is computed from runtime.bin, before it is compressed, using sha1sum in emhfcore/x86/Makefile:

<pre>
sl: runtime common
  #make sl
  # Double-dollar-sign required to cause make to provide literal dollar sign to perl
  # Objective: Create an escaped ASCII string containing the SHA-1 hash of the
  # runtime and pass it to the SL's makefile
  cd sl && $(MAKE) -w all \
     RUNTIME_INTEGRITY_HASH=\""$(shell ( sha1sum ./runtime/runtime.bin | perl -nae '$$F[0] =~ s/(..)/\\\\x$$1/g; print $$F[0];' ))"\"
</pre>

This spits out an ASCII string that uses a bunch of escaped hex characters to encode a 20-byte binary literal.  The double-dollar-signs are escaping a single dollar sign from Make, and the double-backslahes are escaping a single backslash from the shell.  This sets a parameter RUNTIME_INTEGRITY_HASH to the value of the SHA-1 hash of the runtime binary image.  The SL's Makefile then uses this to populate a C preprocessor macro called ___RUNTIME_INTEGRITY_HASH___.  My intention is for the triple-underscore to indicate build-process-generated values.

g_sl_gold is then defined in sl.c, which ends up containing the appropriate hash values, which can be used to do compare the result of a SHA-1 computed over the entire runtime memory area during EMHF bootup.

When the make process descends into the SL, one sees console output like the following:

<pre>
cd sl && make -w all \
		RUNTIME_INTEGRITY_HASH=\""\\x60\\x46\\xb7\\xe9\\xb2\\x94\\xe2\\x17\\x7b\\x98\\x19\\x58\\x2c\\x5c\\x19\\x9b\\x82\\x4e\\x10\\xcf"\"
</pre>

This is the ASCII string containing the 20-byte SHA-1 hash of the runtime for rev 692.  You can get the same value via:

<pre>
jmmccune@pdltmp1 ~/hyp/emhfapp/trunk/code
$ sha1sum emhfcore/x86/runtime/runtime.bin
6046b7e9b294e2177b9819582c5c199b824e10cf *emhfcore/x86/runtime/runtime.bin
</pre>

h3. Secure Loader

* The secure loader is measured by the CPU during creation of the Dynamic Root of Trust (i.e., SKINIT on AMD or GETSEC[SENTER] on Intel).
* The first 64K of the secure loader (sections .sl_header, .text, .data, .bss, and .sl_stack) are measured implicitly during DRTM establishment.
** Section .sl_header will contain different values depending on whether the CPU is AMD or Intel.  
*** AMD: it will contain a 4-byte SLB header, and the remainder will be padding.
*** Intel: the first 3 pages (12K) will be the MLE page tables, and will not actually be part of the measured environment
** Fallout from this is that the expected measurement of the SL will be different depending on whether it was measured by an Intel CPU or an AMD CPU.
*** XXX TODO: Create a script that produces the expected PCR hash values at build time [Jon]

Right now INIT computes an expected PCR-17 value for an AMD system.  This has been tested and found to be correct on the Dell PowerEdge T105, which is the only suitable AMD system I have at the moment.

h2. Boot Messages

Here's an example of some serial debug output and how it relates:

h3. Security-critical (SL checks Runtime)

<pre>
SL: Golden Runtime SHA-1: 60 46 b7 e9 b2 94 e2 17 7b 98 19 58 2c 5c 19 9b 
SL: Golden Runtime SHA-1: 82 4e 10 cf 
hashandprint: processing 0x040bf000 bytes at addr 0x00200000
SL: Computed Runtime SHA-1: 60 46 b7 e9 b2 94 e2 17 7b 98 19 58 2c 5c 19 9b 
SL: Computed Runtime SHA-1: 82 4e 10 cf 
[PERF] hashandprint: elapsed CPU cycles 0x000000019b91a704
</pre>

The "Golden" SHA-1 is the one that was injected during the build process, as described above.  The "Computed" SHA-1 was literally computed by running SHA-1 over the runtime image in memory.  They match!

h3. Debug-useful (Init prints some expected values, and does some computations, though an adversary could cause them to be wrong)

Here's the runtime info, which is again consistent:
