/*
 * XMHF rich guest app for syscalllog hypapp
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <stdio.h>
#include <sys/mman.h>
#include <errno.h>
#include <elf.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <unistd.h>

//////////////////////////////////////////////////////////////////////////////
// base types

typedef unsigned char u8;
typedef unsigned int u32;
typedef unsigned long long int u64;


#define PAGE_SHIFT 12
#define PAGEMAP_LENGTH 8


//////
// vmcall interface
//////
__attribute__ ((always_inline)) static inline void __vmcall(u32 eax, u32 ebx, u32 edx, u32 ecx){
	asm volatile (
			"movl %0, %%eax \r\n"
			"movl %1, %%ebx \r\n"
			"movl %2, %%edx \r\n"
			"movl %3, %%ecx \r\n"
			"vmcall \r\n"
			: /*no output*/
			: "g" (eax), "g" (ebx), "g" (edx), "g" (ecx)
			: "%eax", "%ebx", "%edx", "%ecx"
	);
}


//////
// va_to_pa: virtual to physical address mapping
//////
static u64 va_to_pa(void *vaddr) {
	FILE *pagemap;
	unsigned long offset;
	u64 page_frame_number = 0;

	// open the pagemap file for the current process
	pagemap = fopen("/proc/self/pagemap", "rb");
	if(pagemap == NULL){
		printf("\n%s: unable to open pagemap file. exiting!", __FUNCTION__);
		exit(1);
	}

	// seek to the page that vaddr is on
   offset = (unsigned long)vaddr / getpagesize() * PAGEMAP_LENGTH;
   if(fseek(pagemap, (unsigned long)offset, SEEK_SET) != 0) {
      printf("\n%s: Failed to seek pagemap to proper location", __FUNCTION__);
      exit(1);
   }

   // The page frame number is in bits 0-54 so read the first 7 bytes and clear the 55th bit
   fread(&page_frame_number, 1, PAGEMAP_LENGTH-1, pagemap);

   page_frame_number &= 0x7FFFFFFFFFFFFF;

   fclose(pagemap);

   return (page_frame_number << PAGE_SHIFT);
}


//////
// get syscall page
// return 0 on failure, else the 32-bit virtual address of the syscall page
//////
static u32 getsyscallvaddr(char **envp) {
	Elf32_auxv_t *auxv;

	// walk past all env pointers
    while (*envp++ != NULL)
    	;

    //and find ELF auxiliary vectors
	auxv = (Elf32_auxv_t *) envp;

	for ( ; auxv->a_type != AT_NULL; auxv++)
			if (auxv->a_type == AT_SYSINFO)
					return auxv->a_un.a_val;

    printf("\n%s: warning: no AT_SYSINFO auxv entry found\n", __FUNCTION__);
    return 0;
}



//////
// syscalllog test harness
//////
#define SYSCALLLOG_REGISTER     			0xF0


__attribute__ ((aligned(4096))) u8 syscall_shadowpage[4096];


void do_testsyscalllog(char **envp){
	u32 syscall_vaddr;
	u32 syscall_page_vaddr, syscall_page_paddr;
	u32 syscall_shadowpage_vaddr, syscall_shadowpage_paddr;
	u32 pid;

	syscall_shadowpage_vaddr = &syscall_shadowpage;
	syscall_vaddr = getsyscallvaddr(envp);
	syscall_page_vaddr = syscall_vaddr & 0xFFFFF000UL;

	if(syscall_vaddr == 0){
		printf("\n%s: unable to obtain syscall page vaddr. exiting\n", __FUNCTION__);
		exit(1);
	}

	if(mlock(syscall_page_vaddr, 4096) == -1) {
		  printf("\nFailed to lock syscall page in memory: %s\n", strerror(errno));
		  exit(1);
	}


	if(mlock(syscall_shadowpage_vaddr, 4096) == -1) {
		  printf("\nFailed to lock syscall shadow page in memory: %s\n", strerror(errno));
		  exit(1);
	}


	memcpy(syscall_shadowpage_vaddr, syscall_page_vaddr, 4096);

	if(mprotect(syscall_shadowpage_vaddr, 4096, (PROT_READ | PROT_EXEC)) != 0){
	    printf("\n%s: Could not change syscall shadow page protections: %s\n", __FUNCTION__, strerror(errno));
	    exit(1);
	}


	syscall_page_paddr= va_to_pa(syscall_page_vaddr);
	syscall_shadowpage_paddr =va_to_pa(syscall_shadowpage_vaddr);

	printf("\n%s: syscall page-base vaddr=0x%08x, paddr=0x%08x\n", __FUNCTION__, syscall_page_vaddr, syscall_page_paddr);
	printf("\n%s: syscall shadow page-base vaddr=0x%08x, paddr=0x%08x\n", __FUNCTION__, syscall_shadowpage_vaddr, syscall_shadowpage_paddr);
	printf("\n%s: syscall entry-point at 0x%08x\n", __FUNCTION__, syscall_vaddr);


	__vmcall(SYSCALLLOG_REGISTER, syscall_page_paddr, syscall_shadowpage_vaddr, syscall_shadowpage_paddr);


	//////
	// the following will be logged
	//////
	pid = getpid();

	printf("\n%s: result via getpid() = %x\n", __FUNCTION__, pid);

}



int main(int argc, char **argv, char **envp) {
    printf("\n%s: Proceeding with syscalllog test...", __FUNCTION__);

    do_testsyscalllog(envp);

    printf("\n%s: syscalllog test done", __FUNCTION__);
    printf("\n\n");

    return 0;
}

//////
// building pieces
//////

//__attribute__((aligned(4096))) static u8 testxhhyperdep_page[4096];


//printf("\n%s: DEP page unlocked", __FUNCTION__);

//if(munlock(&testxhhyperdep_page, sizeof(testxhhyperdep_page)) == -1) {
//	  printf("\nFailed to unlock page in memory: %s\n", strerror(errno));
//	  exit(1);
//}

//if(mlock(&testxhhyperdep_page, sizeof(testxhhyperdep_page)) == -1) {
//	  printf("\nFailed to lock page in memory: %s\n", strerror(errno));
//	  exit(1);
//}

//	if(mprotect(&testxhhyperdep_page, sizeof(testxhhyperdep_page), (PROT_READ | PROT_WRITE | PROT_EXEC)) != 0){
//	    printf("\n%s: Could not change page protections: %s\n", __FUNCTION__, strerror(errno));
//	    exit(1);
//	}

//printf("\n%s: result via syscall_getpid() = %x\n", __FUNCTION__, syscall(SYS_getpid));
/*asm volatile	(
		"movl %1, %%eax \r\n"
        "movl %2, %%edx \r\n"
		"call *%%edx \r\n"
		"movl %%eax, %0\r\n"
		: "=g" (pid)	// output
		: "i" (SYS_getpid), "g" (syscall_vaddr)	// input
		: "%eax", "%edx"
);

printf("\n%s: result via vsyscall-getpid() = %x\n", __FUNCTION__, pid);
*/
