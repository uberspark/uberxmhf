#include <linux/init.h>           // macros used to mark up functions e.g. __init __exit
#include <linux/module.h>         // core header for loading LKMs into the kernel
#include <linux/device.h>         // header to support the kernel Driver Model
#include <linux/kernel.h>         // contains types, macros, functions for the kernel
#include <linux/fs.h>             // header for the Linux file system support
#include <asm/uaccess.h>          // required for the copy to user function

//////
// TBD: move into unified header location
//////
typedef struct {
	u32 uhcall_function;
	void *uhcall_buffer;
	u32 uhcall_buffer_len;
} uhcallkmod_param_t;


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

//file operations structure to interface with the above
static struct file_operations fops =
{
   .open = dev_open,
   .write = dev_write,
   .release = dev_release,
};


void hypcall_hvc1(void){
	u32 r_r0, r_r1, r_r2;

	asm volatile
		(	" mov r0, #0x10\r\n"
			" mov r1, #0x11\r\n"
			" mov r2, #0x12\r\n"
			".long 0xE1400071 \r\n"
			" mov %[res_r0], r0 \r\n"
			" mov %[res_r1], r1 \r\n"
			" mov %[res_r2], r2 \r\n"
	           : [res_r0] "=r" (r_r0), [res_r1] "=r" (r_r1), [res_r2] "=r" (r_r2) /* output */
	           : /* inputs */
	           : "r0", "r1", "r2" /* clobber */
	    );

	printk(KERN_INFO "hypcall_init: r0=0x%08x, r1=0x%08x, r2=0x%08x\n", r_r0, r_r1, r_r2);
}



void hypcall_hvc2(u32 address){

	asm volatile
		(	" mov r0, %[in_0]\r\n"
			".long 0xE1400072 \r\n"
	           : /* output */
	           : [in_0] "r" (address) /* inputs */
	           : "r0" /* clobber */
	    );
}

void hypcall_hvc3(u32 address){

	asm volatile
		(	" mov r0, %[in_0]\r\n"
			".long 0xE1400073 \r\n"
	           : /* output */
	           : [in_0] "r" (address) /* inputs */
	           : "r0" /* clobber */
	    );
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

	if(buffer == NULL)
		return -EINVAL;

	if(len != sizeof(uhcallkmod_param_t))
		return -EINVAL;

	uhcallp = (uhcallkmod_param_t *)buffer;

	printk(KERN_INFO "uhcallkmod: dev_write: uhcall_function=0x%08x, uhcall_buffer=0x%08x, uhcall_buffer_len=0x%08x\n",
			uhcallp->uhcall_function, uhcallp->uhcall_buffer, uhcallp->uhcall_buffer_len);


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
