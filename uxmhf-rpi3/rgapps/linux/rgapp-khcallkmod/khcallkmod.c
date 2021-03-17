/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

#include <linux/init.h>           // macros used to mark up functions e.g. __init __exit
#include <linux/module.h>         // core header for loading LKMs into the kernel
#include <linux/device.h>         // header to support the kernel Driver Model
#include <linux/kernel.h>         // contains types, macros, functions for the kernel
#include <linux/fs.h>             // header for the Linux file system support
#include <asm/uaccess.h>          // required for the copy to user function

#include <asm/pgtable.h>

#include <uhcall.h>
#include <uhcalltest.h>

#define  DEVICE_NAME "uhcallkmod"    			//device will appear at /dev/uhcallkmod
#define  CLASS_NAME  "uhcallkmodchar"     	   //we are a character device driver

MODULE_LICENSE("GPL");				//appease the kernel
MODULE_AUTHOR("Amit Vasudevan");
MODULE_DESCRIPTION("Hypercall char driver for uxmhf-rpi3");
MODULE_VERSION("0.1");

static int    major_number;
static int    number_opens = 0;
static struct class*  hypcallcharClass  = NULL;
static struct device* hypcallcharDevice = NULL;

//prototypes for character driver interaction
static int     dev_open(struct inode *, struct file *);
static int     dev_release(struct inode *, struct file *);
static ssize_t dev_write(struct file *, const char *, size_t, loff_t *);
static void uhcallkmod_hvc(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len);

//file operations structure to interface with the above
static struct file_operations fops =
{
   .open = dev_open,
   .write = dev_write,
   .release = dev_release,
};

//prototype for va2pa
static unsigned long va2pa(unsigned long va);  

__attribute__((aligned(4096))) unsigned char buffer[]= {'a', 'b', 'c', 'd'};


static void uhcallkmod_hvc(u32 uhcall_function, void *uhcall_buffer,
		u32 uhcall_buffer_len){

	asm volatile
		(	" mov r0, %[in_0]\r\n"
			" mov r1, %[in_1]\r\n"
			" mov r2, %[in_2]\r\n"
			".long 0xE1400071 \r\n"
				: // outputs
				: [in_0] "r" (uhcall_function), [in_1] "r" (uhcall_buffer), [in_2] "r" (uhcall_buffer_len)  // inouts
	           : "r0", "r1", "r2" //clobber
	    );
}


static unsigned long va2pa(unsigned long va) {
  pgd_t *pgd;
  pud_t *pud;
  pmd_t *pmd;
  pte_t *pte;
  unsigned long pa = 0;
  unsigned long page_addr = 0;
  unsigned long page_offset = 0;

  pgd = pgd_offset(current->mm, va);
  if(pgd_none(*pgd))
    return -1;

  pud = pud_offset(pgd, va);
  if(pud_none(*pud))
    return -1;

  pmd = pmd_offset(pud, va);
  if(pmd_none(*pmd))
    return -1;

  pte = pte_offset_kernel(pmd, va);
  if(pte_none(*pte))
    return -1;

  page_addr = pte_val(*pte) & PAGE_MASK;
  page_offset = va & ~PAGE_MASK;
  pa = page_addr | page_offset;
  
  return pa;
}

static int dev_open(struct inode *inodep, struct file *filep){
   number_opens++;
   printk(KERN_INFO "uhcallkmod: device has been opened %d time(s)\n", number_opens);
   return 0;
}

static int dev_release(struct inode *inodep, struct file *filep){
   number_opens--;
   printk(KERN_INFO "uhcallkmod: device successfully closed\n");
   return 0;
}

static ssize_t dev_write(struct file *filep, const char *buffer, size_t len, loff_t *offset){
	uhcallkmod_param_t *uhcallp;
	unsigned long pa;

	if(buffer == NULL)
		return -EINVAL;

	if(len != sizeof(uhcallkmod_param_t))
		return -EINVAL;

	uhcallp = (uhcallkmod_param_t *)buffer;

	pa = va2pa((u32)(uhcallp->uhcall_buffer));
	
	printk(KERN_INFO "uhcallkmod: dev_write: uhcall_function=0x%08x, uhcall_buffer=0x%08x, uhcall_buffer_len=0x%08x\n",
			uhcallp->uhcall_function, uhcallp->uhcall_buffer, uhcallp->uhcall_buffer_len);

	if(pa != -1){
	   uhcallkmod_hvc(uhcallp->uhcall_function, (void *)pa, uhcallp->uhcall_buffer_len);	
	}
	else{
	   printk("dev_write() pa == -1\n");
	   return -EINVAL;
	}

   return 0;
}

//module initialization function
int uhcallkmod_init(void)
{
	printk(KERN_INFO "uhcallkmod: LOAD\n");
	printk(KERN_INFO "author: amit vasudevan (amitvasudevan@acm.org)\n");

	//try to allocate a major number dynamically
	major_number = register_chrdev(0, DEVICE_NAME, &fops);
	if (major_number<0){
	  printk(KERN_ALERT "uhcallkmod: failed to register a major number\n");
	  return major_number;
	}
	printk(KERN_INFO "uhcallkmod: registered correctly with major number %d\n", major_number);

	// Register the device class
	hypcallcharClass = class_create(THIS_MODULE, CLASS_NAME);
	if (IS_ERR(hypcallcharClass)){
	  unregister_chrdev(major_number, DEVICE_NAME);
	  printk(KERN_ALERT "uhcallkmod: Failed to register device class\n");
	  return PTR_ERR(hypcallcharClass);
	}
	printk(KERN_INFO "uhcallkmod: device class registered correctly\n");

	// register the device driver
	hypcallcharDevice = device_create(hypcallcharClass, NULL, MKDEV(major_number, 0), NULL, DEVICE_NAME);
	if (IS_ERR(hypcallcharDevice)){
	  class_destroy(hypcallcharClass);
	  unregister_chrdev(major_number, DEVICE_NAME);
	  printk(KERN_ALERT "uhcallkmod:Failed to create the device\n");
	  return PTR_ERR(hypcallcharDevice);
	}
	printk(KERN_INFO "uhcallkmod: device class created correctly\n");


	return 0;
}

//module unload function
void uhcallkmod_exit(void)
{
	device_destroy(hypcallcharClass, MKDEV(major_number, 0));     // remove the device
	class_unregister(hypcallcharClass);                          // unregister the device class
	class_destroy(hypcallcharClass);                             // remove the device class
	unregister_chrdev(major_number, DEVICE_NAME);             // unregister the major number
	printk(KERN_INFO "uhcallkmod: UNLOAD\n");
}

module_init(uhcallkmod_init);
module_exit(uhcallkmod_exit);
