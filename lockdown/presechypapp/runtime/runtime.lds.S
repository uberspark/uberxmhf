OUTPUT_FORMAT("pe-i386")
OUTPUT_ARCH(i386)

ENTRY(cstartup)

SECTIONS
{
	. = 0x80000000;

  .text : {
  	*(.s_init)
 		*(.text)
 		. = ALIGN(4096);    
  } =0x9090 

  .data : {
    *(.data)
 		. = ALIGN(4096);    
  } =0x9090 

  .vmxdata : {
    *(.vmxdata)
 		. = ALIGN(4096);    
  } =0x9090 
  
	.stack : {
		*(.stack)
 		. = ALIGN(4096);    
	} =0x9090

}
