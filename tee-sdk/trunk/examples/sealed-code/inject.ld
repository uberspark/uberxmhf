SECTIONS
{
  /* define layout for PAL-related memory sections,                                                                                                                                                                                                ensuring that they are each page aligned and padded.                                                                                                                                                                                        */
  .SCODE ALIGN(0x1000):
  {
    __scode_start = .;
    ___scode_start = .; /* accomodate name mangling on windows */
    *.o(.scode)
    KEEP (*.o(.scode))
    . = ALIGN(0x1000);
    __scode_end = .;
    ___scode_end = .;

    __scode_util_start = .;
    ___scode_util_start = .;
    *.o(.scode_util)
    KEEP (*.o(.scode_util))
    . = ALIGN(0x1000);
    __scode_util_end = .;
    ___scode_util_end = .;

    __sdata_start = .;
    ___sdata_start = .; /* accomodate name mangling on windows */
    *.o(.sdata)
    KEEP (*.o(.sdata))
    . = ALIGN(0x1000);
    __sdata_end = .;
    ___sdata_end = .;
  } =0x90909090 /* fill padding space with no-ops */
}
INSERT AFTER .text;
