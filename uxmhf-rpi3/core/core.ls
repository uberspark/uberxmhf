ENTRY(entry)
MEMORY
{
 ram (rwxai) : ORIGIN = 0x1000000, LENGTH = 0xC00000
 unaccounted (rwxai) : ORIGIN = 0, LENGTH = 0
}
SECTIONS
{
 . = 0x1000000;
    .text : {
     *(.text)
    } > ram = 0x0000
    .data : {
     *(.rodata)
     *(.data)
     *(.bss)
  . = ALIGN(0x4000);
     *(.paligndata)
     . = ALIGN(0x200000);
     *(.palign2mdata)
 } > ram = 0x0000
    .stack : {
     *(.stack)
  . = ALIGN(0x200000);
 } > ram = 0x0000
 /DISCARD/ : {
  *(.ARM.attributes)
  *(.comment)
  *(.ARM.extab)
  *(.ARM.exidx)
  *(.debug_*)
 }
 .unaccounted : {
 *(*)
 } >unaccounted
}
