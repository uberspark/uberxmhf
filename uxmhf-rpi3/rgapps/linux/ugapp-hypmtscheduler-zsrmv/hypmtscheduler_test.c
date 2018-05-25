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

#define  DEVICE_NAME "hypmtschedulerkmod"    			//device will appear at /dev/uhcallkmod
#define  CLASS_NAME  "hypmtschedulerkmodchar"     	   //we are a character device driver

MODULE_LICENSE("GPL");				//appease the kernel
MODULE_AUTHOR("Amit Vasudevan");
MODULE_DESCRIPTION("hypmtscheduler guest kernel-module char driver for uxmhf-rpi3");
MODULE_VERSION("0.1");

static int    major_number;
static int    number_opens = 0;
static struct class*  hypmtschedulercharClass  = NULL;
static struct device* hypmtschedulercharDevice = NULL;

//prototypes for character driver interaction
static int     dev_open(struct inode *, struct file *);
static ssize_t dev_write(struct file *, const char *, size_t, loff_t *);
static int     dev_release(struct inode *, struct file *);
static void __hvc(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len);

//file operations structure to interface with the above
static struct file_operations fops =
{
   .open = dev_open,
   .write = dev_write,
   .release = dev_release,
};


static int dev_open(struct inode *inodep, struct file *filep){
   number_opens++;
   printk(KERN_INFO "hypmtschedulerkmod: device has been opened %d time(s)\n", number_opens);
   return 0;
}

static ssize_t dev_write(struct file *filep, const char *buffer, size_t len, loff_t *offset){
	//return -EINVAL;
	return 0;
}

static int dev_release(struct inode *inodep, struct file *filep){
   number_opens--;
   printk(KERN_INFO "hypmtschedulerkmod: device successfully closed\n");
   return 0;
}


static void __hvc(u32 uhcall_function, void *uhcall_buffer,
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


//module initialization function
int hypmtschedulerkmod_init(void)
{
	printk(KERN_INFO "hypmtschedulerkmod: LOAD\n");
	printk(KERN_INFO "author: amit vasudevan (amitvasudevan@acm.org)\n");

	//try to allocate a major number dynamically
	major_number = register_chrdev(0, DEVICE_NAME, &fops);
	if (major_number<0){
	  printk(KERN_ALERT "hypmtschedulerkmod: failed to register a major number\n");
	  return major_number;
	}
	printk(KERN_INFO "hypmtschedulerkmod: registered correctly with major number %d\n", major_number);

	// Register the device class
	hypmtschedulercharClass = class_create(THIS_MODULE, CLASS_NAME);
	if (IS_ERR(hypmtschedulercharClass)){
	  unregister_chrdev(major_number, DEVICE_NAME);
	  printk(KERN_ALERT "hypmtschedulerkmod: Failed to register device class\n");
	  return PTR_ERR(hypmtschedulercharClass);
	}
	printk(KERN_INFO "hypmtschedulerkmod: device class registered correctly\n");

	// register the device driver
	hypmtschedulercharDevice = device_create(hypmtschedulercharClass, NULL, MKDEV(major_number, 0), NULL, DEVICE_NAME);
	if (IS_ERR(hypmtschedulercharDevice)){
	  class_destroy(hypmtschedulercharClass);
	  unregister_chrdev(major_number, DEVICE_NAME);
	  printk(KERN_ALERT "hypmtschedulerkmod:Failed to create the device\n");
	  return PTR_ERR(hypmtschedulercharDevice);
	}
	printk(KERN_INFO "hypmtschedulerkmod: device class created correctly\n");


	return 0;
}

//module unload function
void hypmtschedulerkmod_exit(void)
{
	device_destroy(hypmtschedulercharClass, MKDEV(major_number, 0));     // remove the device
	class_unregister(hypmtschedulercharClass);                          // unregister the device class
	class_destroy(hypmtschedulercharClass);                             // remove the device class
	unregister_chrdev(major_number, DEVICE_NAME);             // unregister the major number
	printk(KERN_INFO "hypmtschedulerkmod: UNLOAD\n");
}

module_init(hypmtschedulerkmod_init);
module_exit(hypmtschedulerkmod_exit);
