/*
 * XMHF rich guest app for hyperdep hypapp
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include <stdio.h>
#include <sys/mman.h>
#include <errno.h>

typedef unsigned char u8;
typedef unsigned int u32;

//////
// hyperdep test harness

//////////////////////////////////////////////////////////////////////////////
// xhhyperdep test

__attribute__((aligned(4096))) static u8 testxhhyperdep_page[4096];

#define HYPERDEP_ACTIVATEDEP			0xC0
#define HYPERDEP_DEACTIVATEDEP			0xC1

typedef void (*DEPFN)(void);

void do_testxhhyperdep(void){
    u32 gpa = &testxhhyperdep_page;
    DEPFN fn = (DEPFN)gpa;

    testxhhyperdep_page[0] = 0xC3; //ret instruction

    printf("\n%s: Going to activate DEP on page %x", __FUNCTION__, gpa);


    //vmcall(HYPERDEP_ACTIVATEDEP,  0, gpa);

    printf("\n%s: Activated DEP", __FUNCTION__);

    //fn();

    printf("\n%s: Going to de-activate DEP on page %x", __FUNCTION__, gpa);

    //vmcall(HYPERDEP_DEACTIVATEDEP,  0, gpa);

    printf("\n%s: Deactivated DEP", __FUNCTION__);

}



void main(void){
    printf("\n%s: DEP buffer at 0x%08x", __FUNCTION__, &testxhhyperdep_page);

    printf("\n%s: proceeding to lock DEP page...", __FUNCTION__);

    //lock the DEP page in memory so we have it pinned down
	if(mlock(&testxhhyperdep_page, sizeof(testxhhyperdep_page)) == -1) {
		  printf("\nFailed to lock page in memory: %s\n", strerror(errno));
		  exit(1);
	}

    printf("\n%s: DEP page locked", __FUNCTION__);

	do_testxhhyperdep();

    printf("\n%s: proceeding to unlock DEP page...", __FUNCTION__);

    //unlock the DEP page
	if(munlock(&testxhhyperdep_page, sizeof(testxhhyperdep_page)) == -1) {
		  printf("\nFailed to unlock page in memory: %s\n", strerror(errno));
		  exit(1);
	}

    printf("\n%s: DEP page unlocked", __FUNCTION__);


    printf("\n\n");
}
