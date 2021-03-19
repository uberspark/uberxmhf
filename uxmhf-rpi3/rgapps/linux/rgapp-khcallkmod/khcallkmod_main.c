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
#include <linux/numa.h>
#include <linux/gfp.h>
#include <linux/mm.h>
#include <linux/highmem.h>



//to bring in khcall
#include <khcall.h>
#include <i2c-driver.h>
#include <miniuart.h>
#include <debug.h>

//to bring in uhcalltest uapp definitions
#include <uhcalltest.h>

#define  DEVICE_NAME "khcallkmod"    			//device will appear at /dev/uhcallkmod
#define  CLASS_NAME  "khcallkmodchar"     	   //we are a character device driver

MODULE_LICENSE("GPL");				//appease the kernel
MODULE_AUTHOR("Amit Vasudevan");
MODULE_DESCRIPTION("khcall test kernel module");
MODULE_VERSION("0.1");

static int    major_number;
static int    number_opens = 0;
static struct class*  hypcallcharClass  = NULL;
static struct device* hypcallcharDevice = NULL;

//prototypes for character driver interaction
static int     dev_open(struct inode *, struct file *);
static int     dev_release(struct inode *, struct file *);
static ssize_t dev_write(struct file *, const char *, size_t, loff_t *);

//file operations structure to interface with the above
static struct file_operations fops =
{
   .open = dev_open,
   .write = dev_write,
   .release = dev_release,
};


static int dev_open(struct inode *inodep, struct file *filep){
   number_opens++;
   printk(KERN_INFO "khcallkmod: device has been opened %d time(s)\n", number_opens);
   return 0;
}

static int dev_release(struct inode *inodep, struct file *filep){
   number_opens--;
   printk(KERN_INFO "khcallkmod: device successfully closed\n");
   return 0;
}

static ssize_t dev_write(struct file *filep, const char *buffer, size_t len, loff_t *offset){
	printk(KERN_INFO "khcallkmod: dev_write: nothing to do!\n");
	return 0;
}


__attribute__((aligned(4096))) unsigned char buffer[]= {'a', 'b', 'c', 'd'};
__attribute__((section(".data"))) __attribute__((aligned(4096))) i2c_driver_param_t i2c_drv_param;
#define HMAC_DIGEST_SIZE 32

//module initialization function
int khcallkmod_init(void)
{
	printk(KERN_INFO "khcallkmod: LOAD\n");
	printk(KERN_INFO "author: amit vasudevan (amitvasudevan@acm.org)\n");

	//try to allocate a major number dynamically
	major_number = register_chrdev(0, DEVICE_NAME, &fops);
	if (major_number<0){
	  printk(KERN_ALERT "khcallkmod: failed to register a major number\n");
	  return major_number;
	}
	printk(KERN_INFO "khcallkmod: registered correctly with major number %d\n", major_number);

	// Register the device class
	hypcallcharClass = class_create(THIS_MODULE, CLASS_NAME);
	if (IS_ERR(hypcallcharClass)){
	  unregister_chrdev(major_number, DEVICE_NAME);
	  printk(KERN_ALERT "khcallkmod: Failed to register device class\n");
	  return PTR_ERR(hypcallcharClass);
	}
	printk(KERN_INFO "khcallkmod: device class registered correctly\n");

	// register the device driver
	hypcallcharDevice = device_create(hypcallcharClass, NULL, MKDEV(major_number, 0), NULL, DEVICE_NAME);
	if (IS_ERR(hypcallcharDevice)){
	  class_destroy(hypcallcharClass);
	  unregister_chrdev(major_number, DEVICE_NAME);
	  printk(KERN_ALERT "khcallkmod:Failed to create the device\n");
	  return PTR_ERR(hypcallcharDevice);
	}
	printk(KERN_INFO "khcallkmod: device class created correctly\n");

	//test khcall
/*	{
		struct page *k_page1;
		uhcalltest_param_t *uhctp;
		u32 i;
		u8 ch='a';

      	k_page1 = alloc_page(GFP_KERNEL | __GFP_ZERO);
        uhctp = (uhcalltest_param_t *)page_address(k_page1);

		if(!uhctp){
			printk(KERN_INFO "khcallkmod: could not alloc_page\n");
			return -1;
		}
		printk(KERN_INFO "khcallkmod: allocated buffer\n");

		//prepare test input buffer
		printk(KERN_INFO "%s: populating in[] and out[]...\n", __FUNCTION__);
		for(i=0; i < 16; i++)
	   		uhctp->in[i] = ch + i;
		memset(&uhctp->out, 0, 16);

		printk(KERN_INFO "dumping in[]...\n");
		for(i=0; i < 16; i++)
			printk(KERN_INFO "%c", uhctp->in[i]);
		printk(KERN_INFO "\n");

		if(!khcall(UAPP_UHCALLTEST_FUNCTION_TEST, uhctp, sizeof(uhcalltest_param_t)))
			printk(KERN_INFO "hypercall FAILED\n");
		else
			printk(KERN_INFO "hypercall SUCCESS\n");

		printk(KERN_INFO "dumping out[]...\n");
		for(i=0; i < 16; i++)
			printk(KERN_INFO "%c", uhctp->out[i]);
		printk(KERN_INFO "\n");

		printk(KERN_INFO "khcallkmod: done!\n");
      	__free_page(k_page1);
	} */ 

        // test HMAC call
        {
#if defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_PL011__) || defined (__UBERSPARK_UOBJCOLL_CONFIGDEF_ENABLE_UART_MINI__)
	//initialize uart
	uart_init();
#endif
            unsigned long digest_size = HMAC_DIGEST_SIZE;
            struct page *k_page1;
            struct page *k_page2;
            unsigned char *digest_result;
	    char *tmp;
            i2c_driver_param_t *ptr_i2c_driver = &i2c_drv_param; 
            // allocate kernel pages
            k_page1 = alloc_page(GFP_KERNEL | __GFP_ZERO);
            if(!k_page1){
               printk("alloc_page() failed for k_page1\n");
	       return -ENOMEM;
            }
            digest_result = (void *)page_address(k_page1);
            k_page2 = alloc_page(GFP_KERNEL | __GFP_ZERO);
            if(!k_page2){
               printk("alloc_page() failed for k_page2\n");
	       return -ENOMEM;
            }
            tmp = (void *)page_address(k_page2);
            tmp[0]='a'; tmp[1]='b';tmp[2]='c';tmp[3]='d';tmp[4]='e';
            tmp[5]='f'; tmp[6]='g';tmp[7]='h';tmp[8]='i';tmp[9]='j';
            ptr_i2c_driver = &i2c_drv_param; 
            ptr_i2c_driver->in_buffer_va = (uint32_t) tmp;
            ptr_i2c_driver->len = 10;
            ptr_i2c_driver->out_buffer_va = (uint32_t) digest_result;
            if(!khcall(UAPP_I2C_DRIVER_FUNCTION_TEST, ptr_i2c_driver, sizeof(i2c_driver_param_t)))
               printk("hypercall FAILED\n");
            else{  
               int i;
               printk("hypercall SUCCESS \n"); 
	       printk(KERN_INFO "dumping in[]...\n");
	       for(i=0; i < 10; i++)
		  printk(KERN_INFO "%c", ((char *)ptr_i2c_driver->in_buffer_va)[i]);
	       printk(KERN_INFO "\n");
               printk("Dumping HMAC bytes \n"); 
               for(i=0;i<digest_size;i++){
		  printk(KERN_INFO "0x%X", digest_result[i]);
               } 
            }   
            __free_page(k_page1);
            __free_page(k_page2);
        }


	return 0;
}

//module unload function
void khcallkmod_exit(void)
{
	device_destroy(hypcallcharClass, MKDEV(major_number, 0));     // remove the device
	class_unregister(hypcallcharClass);                          // unregister the device class
	class_destroy(hypcallcharClass);                             // remove the device class
	unregister_chrdev(major_number, DEVICE_NAME);             // unregister the major number
	printk(KERN_INFO "khcallkmod: UNLOAD\n");
}

module_init(khcallkmod_init);
module_exit(khcallkmod_exit);
