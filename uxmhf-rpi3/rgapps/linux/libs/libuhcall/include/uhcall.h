/*
	libuhcall header

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __UHCALL_H__
#define __UHCALL_H__

#define UHCALL_PM_PAGE_SHIFT 	12
#define UHCALL_PM_LENGTH		 8


#ifndef __ASSEMBLY__

typedef struct {
	unsigned long uhcall_function;
	void *uhcall_buffer;
	unsigned long uhcall_buffer_len;
} uhcallkmod_param_t;


bool uhcall_va2pa(void *vaddr, uint64_t *paddr);


#endif // __ASSEMBLY__



#endif //__UHCALL_H__
