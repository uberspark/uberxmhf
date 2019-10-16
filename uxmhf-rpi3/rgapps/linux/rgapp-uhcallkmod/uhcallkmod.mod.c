#include <linux/module.h>
#include <linux/vermagic.h>
#include <linux/compiler.h>

MODULE_INFO(vermagic, VERMAGIC_STRING);

__visible struct module __this_module
__attribute__((section(".gnu.linkonce.this_module"))) = {
	.name = KBUILD_MODNAME,
	.init = init_module,
#ifdef CONFIG_MODULE_UNLOAD
	.exit = cleanup_module,
#endif
	.arch = MODULE_ARCH_INIT,
};

static const struct modversion_info ____versions[]
__used
__attribute__((section("__versions"))) = {
	{ 0xb344870e, __VMLINUX_SYMBOL_STR(module_layout) },
	{ 0x919edf7c, __VMLINUX_SYMBOL_STR(class_unregister) },
	{ 0x18391aa, __VMLINUX_SYMBOL_STR(device_destroy) },
	{ 0x5a041bb8, __VMLINUX_SYMBOL_STR(class_destroy) },
	{ 0x6bc3fbc0, __VMLINUX_SYMBOL_STR(__unregister_chrdev) },
	{ 0x1490a67c, __VMLINUX_SYMBOL_STR(device_create) },
	{ 0xf39cacaa, __VMLINUX_SYMBOL_STR(__class_create) },
	{ 0xfb88e8b1, __VMLINUX_SYMBOL_STR(__register_chrdev) },
	{ 0x2e5810c6, __VMLINUX_SYMBOL_STR(__aeabi_unwind_cpp_pr1) },
	{ 0x27e1a049, __VMLINUX_SYMBOL_STR(printk) },
	{ 0xb1ad28e0, __VMLINUX_SYMBOL_STR(__gnu_mcount_nc) },
};

static const char __module_depends[]
__used
__attribute__((section(".modinfo"))) =
"depends=";


MODULE_INFO(srcversion, "727A39D20172DCFD649473D");
