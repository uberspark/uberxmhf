#include <types.h>
#include <arm8-32.h>
#include <bcm2837.h>
#include <miniuart.h>
#include <debug.h>

#define MAXPERFITER		65536

extern u32 g_svcvtable[];

extern void cpumodeswitch_svc2usr(u32 address);


/* performance monitoring stuff */
static inline u32 pmu_getcyclecount(void){
  u32 value;
  // read CCNT register
  asm volatile ("mrc p15, 0, %0, c9, c13, 0\t\n": "=r"(value));
  return value;
}

void pmu_initperfcounters(u32 reset, u32 enable_divider){
  //in general enable all counters (including cycle counter)
  u32 value = 1;

  //peform reset if indicated
  if (reset){
    value |= 2;     // reset all counters to zero.
    value |= 4;     // reset cycle counter to zero.
  }

  //if divider enabled then enable divide by 64
  if (enable_divider)
    value |= 8;

  //program the performance-counter control-register
  asm volatile ("mcr p15, 0, %0, c9, c12, 0\t\n" :: "r"(value));

  //enable all counters
  asm volatile ("mcr p15, 0, %0, c9, c12, 1\t\n" :: "r"(0x8000000f));

  //enable USR mode access to performance counters
  asm volatile ("mcr p15, 0, %0, c9, c14, 0\t\n" :: "r"(0x0000000f));


  // clear overflows:
  asm volatile ("MCR p15, 0, %0, c9, c12, 3\t\n" :: "r"(0x8000000f));
}

u32 pmu_cyclecountoverhead=0;

/**/


u32 pmu_getcyclecount_overhead(void){
	u32 i;
	u32 opcycles_start, opcycles_end;
	u32 totalopcycles=0;

	for(i=0; i < MAXPERFITER; i++){
		opcycles_start = pmu_getcyclecount();
		opcycles_end = pmu_getcyclecount();
		totalopcycles += (opcycles_end - opcycles_start);
	}

	//bcm2837_miniuart_puts(" pmu_getcyclecount_overhead=0x");
	//debug_hexdumpu32( totalopcycles/4096 );

	return (totalopcycles/MAXPERFITER);
}


void svc_handler(void){
	//bcm2837_miniuart_puts("uXMHF-rpi3: guestos: SVC_handler [IN]\n");
	//bcm2837_miniuart_puts("uXMHF-rpi3: guestos: SVC_handler [OUT]\n");
	//hypcall();
}


void usr_main(void){
	u32 cpsr, i;
	u32 opcycles_start;
	u32 opcycles_end;
	u32 totalopcycles=0;

	bcm2837_miniuart_puts("uXMHF-rpi3: guestos: usr_main [IN]\n");

	cpsr = sysreg_read_cpsr();
	bcm2837_miniuart_puts(" CPSR[mode]= ");
	debug_hexdumpu32((cpsr & 0xF));

	bcm2837_miniuart_puts("uxmhf-rpi3: guestos: proceeding to test supervisor call (SVC) in SVC mode...\n");

	for(i=0; i < MAXPERFITER; i++){
		opcycles_start=pmu_getcyclecount();
		svccall();
		opcycles_end=pmu_getcyclecount();
		totalopcycles += (opcycles_end - opcycles_start);
	}

	bcm2837_miniuart_puts("uxmhf-rpi3: guestos: successful return after supervisor call test.\n");

	bcm2837_miniuart_puts(" op cycles=0x");
	debug_hexdumpu32( (totalopcycles/MAXPERFITER) - pmu_getcyclecount_overhead());


	bcm2837_miniuart_puts("uXMHF-rpi3: guestos: Halting!\n");
	HALT();
}



void main(u32 r0, u32 id, struct atag *at){
	//struct atag *pat;
	//bcm2837_miniuart_init();
	u32 cpsr;
	u32 vbar;
	u32 opcycles_start, opcycles_end, i;
	u32 totalopcycles=0;
	u32 sctlr;

	bcm2837_miniuart_puts("uXMHF-rpi3: guestos: Hello World!\n");
	bcm2837_miniuart_puts(" r0= ");
	debug_hexdumpu32(r0);
	bcm2837_miniuart_puts(" id= ");
	debug_hexdumpu32(id);
	bcm2837_miniuart_puts(" ATAGS= ");
	debug_hexdumpu32(at);

	cpsr = sysreg_read_cpsr();
	bcm2837_miniuart_puts(" CPSR[mode]= ");
	debug_hexdumpu32((cpsr & 0xF));

	sctlr = sysreg_read_sctlr();
	bcm2837_miniuart_puts(" SCTLR before= ");
	debug_hexdumpu32(sctlr);

	sctlr |= (1 << 12);	//enable instruction caching
	sctlr |= (1 << 2);		//enable data caching

	sysreg_write_sctlr(sctlr);

	sctlr = sysreg_read_sctlr();
	bcm2837_miniuart_puts(" SCTLR after= ");
	debug_hexdumpu32(sctlr);


	vbar = sysreg_read_vbar();
	bcm2837_miniuart_puts(" VBAR before= ");
	debug_hexdumpu32(vbar);

	bcm2837_miniuart_puts(" g_svcvtable at= ");
	debug_hexdumpu32((u32)&g_svcvtable);
	sysreg_write_vbar((u32)&g_svcvtable);

	vbar = sysreg_read_vbar();
	bcm2837_miniuart_puts(" loaded VBAR with g_svcvtable; VBAR after= ");
	debug_hexdumpu32(vbar);



	//init performance counter
	pmu_initperfcounters(1, 0);





	bcm2837_miniuart_puts("uxmhf-rpi3: guestos: proceeding to test hypercall (HVC) in SVC mode...\n");

	for(i=0; i < MAXPERFITER; i++){
		opcycles_start=pmu_getcyclecount();
		hypcall();
		opcycles_end=pmu_getcyclecount();
		totalopcycles += (opcycles_end - opcycles_start);
	}


	bcm2837_miniuart_puts("uxmhf-rpi3: guestos: successful return after hypercall test.\n");

	bcm2837_miniuart_puts(" op cycles=0x");
	debug_hexdumpu32( (totalopcycles/MAXPERFITER) - pmu_getcyclecount_overhead());

	bcm2837_miniuart_puts("uxmhf-rpi3: guestos: proceeding to switch to USR mode...\n");
	cpumodeswitch_svc2usr(&usr_main);

	bcm2837_miniuart_puts("uXMHF-rpi3: guestos: All done. Halting!\n");
	HALT();

}


