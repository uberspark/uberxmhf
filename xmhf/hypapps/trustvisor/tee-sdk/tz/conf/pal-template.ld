SECTIONS
{
  /* define layout for PAL-related memory sections,
     ensuring that they are each page aligned and padded.
   */
  .SCODE ALIGN(0x1000):
  {
    __scode_start = .;
    ___scode_start = .; /* accomodate name mangling on windows */
    PAL_NAME.pal.o(.text)
    PAL_NAME.pal.o(.scode) /* backwards compat */
    PAL_NAME.pal.o(.SCODE) /* backwards compat */
    PAL_NAME.pal.o(.stext) /* backwards compat */
    PAL_NAME.pal.o(.STEXT) /* backwards compat */
    . = ALIGN(0x1000);
    __scode_end = .;
    ___scode_end = .;
  } =0x90909090 /* fill padding space with no-ops */

  .SDATA ALIGN(0x1000):
  {
    __sdata_start = .;
    ___sdata_start = .; 
    PAL_NAME.pal.o(.sdata) /* backwards compat */
    PAL_NAME.pal.o(.SDATA) /* backwards compat */
    PAL_NAME.pal.o(.rodata*)
    PAL_NAME.pal.o(.rdata) /* win32 read-only data */
    PAL_NAME.pal.o(.data)
    PAL_NAME.pal.o(.bss)
    . = ALIGN(0x1000);
    __sdata_end = .;
    ___sdata_end = .;
  } =0x00000000 /* fill padding space with zeros */
} INSERT AFTER .text;
