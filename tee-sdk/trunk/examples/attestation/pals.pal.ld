SECTIONS
{
  /* define layout for PAL-related memory sections,
     ensuring that they are each page aligned and padded.
   */
  .SCODE ALIGN(0x1000):
  {
    __scode_start = .;
    ___scode_start = .; /* accomodate name mangling on windows */
    pals.pal.o(.text)
    pals.pal.o(.scode) /* backwards compat */
    pals.pal.o(.SCODE) /* backwards compat */
    pals.pal.o(.stext) /* backwards compat */
    pals.pal.o(.STEXT) /* backwards compat */
    . = ALIGN(0x1000);
    __scode_end = .;
    ___scode_end = .;
  } =0x90909090 /* fill padding space with no-ops */

  .STEXT ALIGN(0x1000):
  {
    __stext_start = .;
    ___stext_start = .; /* accomodate name mangling on windows */
    . = ALIGN(0x1000);
    __stext_end = .;
    ___stext_end = .;
  } =0x90909090 /* fill padding space with no-ops */

  .SDATA ALIGN(0x1000):
  {
    __sdata_start = .;
    ___sdata_start = .; 
    pals.pal.o(.sdata) /* backwards compat */
    pals.pal.o(.SDATA) /* backwards compat */
    pals.pal.o(.rodata*)
    pals.pal.o(.data)
    pals.pal.o(.bss)
    . = ALIGN(0x1000);
    __sdata_end = .;
    ___sdata_end = .;
  } =0x00000000 /* fill padding space with zeros */
} INSERT AFTER .text;
