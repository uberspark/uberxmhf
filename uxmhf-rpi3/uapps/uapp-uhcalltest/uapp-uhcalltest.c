/*
	uhcalltest hypapp
	guest hypercall test hypapp

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#include <uhcalltest.h>

#define MAX_LVL1_ENTRIES	4096
#define MAX_LVL2_ENTRIES	256

#define SIZEOF_LVL1_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory
#define SIZEOF_LVL2_ENTRY_MAP	(1024*1024)	//each lvl1 entry maps to 1MB of memory

/*
uint32_t va2pa(uint32_t va){
	u32 ttbcr;
	u32 ttbr0;
	u32 ttbr1;
	u32 pdbr;
	u32 *lvl1tbl;	//4096 entries
	u32 i;
	u32 lvl1tbl_index;
	u32 lvl2tbl_index;
	u32 lvl1tbl_entry;
	u32 lvl2tbl_entry;
	u32 *lvl2tbl;

	_XDPRINTFSMP_("%s: ENTER: va=0x%08x\n", __func__, va);

	ttbcr = sysreg_read_ttbcr();
	_XDPRINTFSMP_("%s: ttbcr=0x%08x\n", __func__, ttbcr);

	ttbr0 = sysreg_read_ttbr0();
	_XDPRINTFSMP_("%s: ttbr0=0x%08x\n", __func__, ttbr0);

	ttbr1 = sysreg_read_ttbr1();
	_XDPRINTFSMP_("%s: ttbr1=0x%08x\n", __func__, ttbr1);


	pdbr = ttbr0 & 0xFFFFFF80UL;	//strip lower 7 bits
	_XDPRINTFSMP_("%s: pdbr=0x%08x\n", __func__, pdbr);

	lvl1tbl_index = va/SIZEOF_LVL1_ENTRY_MAP;
	lvl2tbl_index = (va % SIZEOF_LVL1_ENTRY_MAP) / 4096;

	lvl1tbl = (u32 *)pdbr;

	_XDPRINTFSMP_("%s: lvl1tbl=0x%08x\n", __func__, lvl1tbl);

	lvl1tbl_entry = lvl1tbl[lvl1tbl_index];

	_XDPRINTFSMP_("%s: lvl1tbl_index=%u, lvl1tbl entry=0x%08x\n", __func__,
			lvl1tbl_index, lvl1tbl_entry);

	if( (lvl1tbl_entry & 0x00000003UL) != 0x1){
		_XDPRINTFSMP_("%s: unhandled lvl1tbl_entry. Halting!\n", __func__);
		HALT();
	}

	lvl2tbl = (u32 *) (u32)( lvl1tbl_entry & 0xFFFFFE00UL);

	_XDPRINTFSMP_("%s: lvl2tbl=0x%08x\n", __func__, lvl2tbl);

	lvl2tbl_entry = lvl2tbl[lvl2tbl_index];

	_XDPRINTFSMP_("%s: lvl2tbl_index=%u, lvl2tbl entry=0x%08x\n", __func__,
			lvl2tbl_index, lvl2tbl_entry);

	_XDPRINTFSMP_("%s: WiP\n", __func__);
}
*/


uint32_t va2pa(uint32_t va){
	u32 par;
	u8 *ch;

	_XDPRINTFSMP_("%s: ENTER: va=0x%08x\n", __func__, va);

	sysreg_tlbiallh();
#if 0
	sysreg_ats12nsour(va);
	par = sysreg_read_par();
#endif

	sysreg_ats1cpr(va);
	par = sysreg_read_par();

	_XDPRINTFSMP_("%s: PAR=0x%08x\n", __func__, par);

	if(par & 0x1){
		_XDPRINTFSMP_("%s: Fault in address translation. Halting!\n", __func__);
		HALT();
	}

	par &= 0xFFFFF000UL;

	_XDPRINTFSMP_("%s: PAR after pruning=0x%08x\n", __func__, par);

#if 0
	sysreg_ats1cpr(va);
	par = sysreg_read_par();

	_XDPRINTFSMP_("%s: PAR(ats1cpr)=0x%08x\n", __func__, par);
#endif

	ch = (u8 *)par;

	_XDPRINTFSMP_("%s: ch=%c\n", __func__, *ch);

	_XDPRINTFSMP_("%s: WiP\n", __func__);
}



//return true if handled the hypercall, false if not
bool uapp_uhcalltest_handlehcall(u32 uhcall_function, void *uhcall_buffer, u32 uhcall_buffer_len){
	uhcalltest_param_t *uhctp;
	uint32_t i;

	if(uhcall_function != UAPP_UHCALLTEST_FUNCTION_TEST)
		return false;

	_XDPRINTFSMP_("%s: hcall: uhcall_function=0x%08x, uhcall_buffer=0x%08x, uhcall_buffer_len=0x%08x\n", __func__,
			uhcall_function, uhcall_buffer, uhcall_buffer_len);

	va2pa((uint32_t)uhcall_buffer);

#if 0
	uhctp = (uhcalltest_param_t *)uhcall_buffer;
   _XDPRINTFSMP_("dumping uhctp->in[]...\n");
   for(i=0; i < 16; i++)
	   _XDPRINTFSMP_("%c", uhctp->in[i]);
   _XDPRINTFSMP_("\ndumped uhctp->in[]\n");

   memcpy(&uhctp->out, &uhctp->in, 16);

   _XDPRINTFSMP_("dumping uhctp->out[]...\n");
   for(i=0; i < 16; i++)
	   _XDPRINTFSMP_("%c", uhctp->out[i]);
   _XDPRINTFSMP_("\ndumped uhctp->out[]\n");
#endif

	return true;
}
