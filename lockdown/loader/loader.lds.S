OUTPUT_FORMAT("pe-i386")
OUTPUT_ARCH(i386)

ENTRY(loader_start)

SECTIONS
{
	. = 0x1E00000;
	.multiboot_header : {
		*(.multiboot_header)
 		. = ALIGN(4096);    
	} = 0x9090

  .text : {
  	*(.text)
 		. = ALIGN(4096);    
  } =0x9090 

  .data : {
    *(.data)
 		. = ALIGN(4096);    
  } =0x9090 
  
	.stack : {
		*(.stack)
 		. = ALIGN(4096);    
	} =0x9090

}
