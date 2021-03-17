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

//to bring in khcall
#include <khcall.h>

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
