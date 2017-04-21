#include <linux/module.h>
#include <linux/kernel.h>



void hypcall_hvc(void){
	u32 r_r0, r_r1, r_r2;

	asm volatile
		(	" mov r0, #0x10\r\n"
			" mov r1, #0x11\r\n"
			" mov r2, #0x12\r\n"
			".long 0xE1400070 \r\n"
			" mov %[res_r0], r0 \r\n"
			" mov %[res_r1], r1 \r\n"
			" mov %[res_r2], r2 \r\n"
	           : [res_r0] "=r" (r_r0), [res_r1] "=r" (r_r1), [res_r2] "=r" (r_r2) /* output */
	           : /* inputs */
	           : "r0", "r1", "r2" /* clobber */
	    );

	printk(KERN_INFO "hypcall_init: r0=0x%08x, r1=0x%08x, r2=0x%08x\n", r_r0, r_r1, r_r2);
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
