#include <types.h>
#include <target.h>
#include <print.h>
#include <multiboot.h>
#include <str.h>
#include <error.h>

typedef void (*runtimeentry_f)(void);

void cstartup(unsigned long magic, unsigned long addr);
//==============================================================================
//loader startup
//==============================================================================
void cstartup(unsigned long magic, unsigned long addr){
	multiboot_info_t *mbi;
	module_t *mod_array;
	u32 mods_count, i;
	//runtimeentry_f runtimeentry;

#ifdef __DEBUG_SERIAL__		
	init_uart();
#endif

#ifdef __DEBUG_VGA__
	vgamem_clrscr();
#endif
	
  mbi = (multiboot_info_t *) addr;
  mod_array = (module_t*)mbi->mods_addr;
  mods_count = mbi->mods_count;

	printf("\nLoader Initializing (magic=0x%08lx, infoaddr=0x%08lx)...",
		magic, addr);
	printf("\nTotal mods:%u, list follows...", mods_count);
	for(i=0; i < mods_count; i++)
		printf("\nModule %u: 0x%08x-0x%08x (size=0x%08x)", i,
			(u32)mod_array[i].mod_start, (u32)mod_array[i].mod_end,
			(u32)mod_array[i].mod_end-(u32)mod_array[i].mod_start );


#if defined(__CONF_GUESTOS_LINUX__) 
	printf("\nGuest OS is Linux: Relocating Kernel and Initrd...");
	relocate(mbi);
	printf("Done.");
#endif

	
	//relocate runtime to correct address
	memcpy((void*)__TARGET_BASE, (void*)mod_array[0].mod_start, 
		(u32)mod_array[0].mod_end-(u32)mod_array[0].mod_start);
	
	//transfer control to runtime
	{
		u32 bootmodule_start, bootmodule_size;
		u32 bootmodule1_start, bootmodule1_size;
		
		bootmodule_start = (u32)mod_array[1].mod_start;
		bootmodule_size = (u32)mod_array[1].mod_end - (u32)mod_array[1].mod_start;
		
		if(mods_count > 2){
			bootmodule1_start = (u32)mod_array[2].mod_start;
			bootmodule1_size = (u32)mod_array[2].mod_end - (u32)mod_array[2].mod_start;
		}
		
//#if !defined(__CONF_GUESTOS_LINUX__) 
		
		asm volatile ( "movl %0, %%esi \r\n"
									 "movl %1, %%ebx \r\n"
									 "movl %2, %%ecx \r\n"
									 "movl %3, %%edx \r\n"
									 "movl %4, %%edi \r\n"
									 "jmp %%edi\r\n"
					 : // no outputs
					 : "g"(bootmodule_start), "g"(bootmodule_size), "g"(bootmodule1_start), "g"(bootmodule1_size), "i"(__TARGET_BASE)
					 : "%esi", "%ebx", "%ecx", "%edx", "%edi");

//#else
//		printf("\nBooting linux now...");
//		boot_linux();

//#endif


	}

	//we should never get here
	printf("\nHALT: loader, we should never get here!");
	HALT();
}
