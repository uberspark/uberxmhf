/*
	hypercall test application

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __UHCALLTEST_H__
#define __UHCALLTEST_H__

#define UAPP_UHCALLTEST_FUNCTION_TEST	10

#ifndef __ASSEMBLY__

typedef struct {
	uint8_t in[16];
	uint8_t out[16];
}uhcalltest_param_t;

#endif // __ASSEMBLY__



#endif //__UHCALLTEST_H__
