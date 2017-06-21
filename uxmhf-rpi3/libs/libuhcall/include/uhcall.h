/*
	libuhcall header

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __UHCALL_H__
#define __UHCALL_H__


#ifndef __ASSEMBLY__

typedef struct {
	unsigned long uhcall_function;
	void *uhcall_buffer;
	unsigned long uhcall_buffer_len;
} uhcallkmod_param_t;


#endif // __ASSEMBLY__



#endif //__UHCALL_H__
