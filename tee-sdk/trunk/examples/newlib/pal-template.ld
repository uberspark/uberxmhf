SECTIONS
{
  /* define layout for PAL-related memory sections,
     ensuring that they are each page aligned and padded.
   */
  .SCODE ALIGN(0x1000):
  {
    __scode_start = .;
    ___scode_start = .; /* accomodate name mangling on windows */
    PAL_NAME.pal(.text)
    . = ALIGN(0x1000);
    __scode_end = .;
    ___scode_end = .;
  } =0x90909090 /* fill padding space with no-ops */

  .STEXT ALIGN(0x1000):
  {
    __stext_start = .;
    ___stext_start = .; /* accomodate name mangling on windows */
    PAL_NAME.pal(.text)
    . = ALIGN(0x1000);
    __stext_end = .;
    ___stext_end = .;
  } =0x90909090 /* fill padding space with no-ops */

  .SDATA ALIGN(0x1000):
  {
    __sdata_start = .;
    ___sdata_start = .; 
    PAL_NAME.pal(.rodata)
    PAL_NAME.pal(.data)
    PAL_NAME.pal(.bss)
    . = ALIGN(0x1000);
    __sdata_end = .;
    ___sdata_end = .;
  } =0x00000000 /* fill padding space with zeros */
} INSERT AFTER .text;
