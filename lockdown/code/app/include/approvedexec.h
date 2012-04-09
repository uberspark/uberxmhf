//approved execution within trusted environment declarations/constants
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __APPROVEDEXEC_H__
#define __APPROVEDEXEC_H__

#define	MAX_FULL_HASHLIST_ELEMENTS		(75000)							//maximum no. of 20-byte SHA-1 records for
																		//full code-page hashes

#define	MAX_PARTIAL_HASHLIST_ELEMENTS	(15000)							//maximum no. of 20-byte SHA-1 records for
																		//partial code-page hashes


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

void approvedexec_setup(VCPU *vcpu, APP_PARAM_BLOCK *apb);
u32 approvedexec_checkhashes(u32 pagebase_paddr, u32 *index, u32 *fullhash);
u32 windows_verifycodeintegrity(VCPU *vcpu, u32 paddr, u32 vaddrfromcpu);
u32 approvedexec_handleevent(VCPU *vcpu, struct regs *r, 
  u64 gpa, u64 gva, u64 violationcode);


#endif //__APPROVEDEXEC_H__
