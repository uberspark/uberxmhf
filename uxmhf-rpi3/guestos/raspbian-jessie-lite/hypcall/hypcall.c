#include <linux/module.h>
#include <linux/kernel.h>



void hypcall_hvc(void){

	asm volatile
		(	" mov r0, #0x10\r\n"
			" mov r1, #0x11\r\n"
			" mov r2, #0x12\r\n"
			".long 0xE1400070 \r\n"
	           : /* output */
	           : /* inputs */
	           : "r0", "r1", "r2" /* clobber */
	    );

}



//module initialization function
int hypcall_init(void)
{
	printk(KERN_INFO "hypcall_init: LOAD\n");
	printk(KERN_INFO "author: amit vasudevan (amitvasudevan@acm.org)\n");
	printk(KERN_INFO "hypcall_init: preparing to invoke hypercall...\n");
	hypcall_hvc();
	printk(KERN_INFO "hypcall_init: came back after hypercall...\n");
	return 0;
}

//module unload function
void hypcall_exit(void)
{
	printk(KERN_INFO "hypcall_init: UNLOAD\n");
}

module_init(hypcall_init);
module_exit(hypcall_exit);
