//approved execution within trusted environment declarations/constants
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __APPROVEDEXEC_H__
#define __APPROVEDEXEC_H__

extern u32 ax_debug_flag;

//debugging macro for approvedexec module
#define AX_DEBUG(x) {if (ax_debug_flag) printf x;}

struct hashinfo {
	char *name;
	u32 pagenum;
	u32 pagebase;
	u32 pageoffset;
	u32 size;
	u8  shanum[20];
} __attribute__((packed));

extern struct hashinfo hashlist[];
extern u32 hashlist_totalelements;

//u32 approvedexec_checkhashes(u32 pagebase_paddr);
u32 windows_verifycodeintegrity(VCPU *vcpu, u32 paddr, u32 vaddrfromcpu);


#endif //__APPROVEDEXEC_H__