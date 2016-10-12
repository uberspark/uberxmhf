#define RET_EIP 0xabcd0000

extern unsigned int xmhfhwm_cpu_gprs_edx, xmhfhwm_cpu_gprs_eax;
extern void ci_pushl(unsigned int);
extern unsigned long long casm_funccall(unsigned int x, unsigned int y);
extern unsigned long int xmhfhwm_cpu_gprs_esp;

unsigned long long casm_funkyfunc(unsigned int x, unsigned int y){
	ci_ret();
	ci_label("x");

}

unsigned long long casm_funkyfunc_2(unsigned int x, unsigned int y){
	ci_jmplabel("y");
	ci_jc("y");
	ci_jnc("y");
	ci_jz("y");
	ci_jnz("y");
	ci_je("y");
	ci_jbe("y");
	ci_ja("y");

	ci_call("casm_funkyfunc");
	ci_call("casm_funccall");
	ci_call("subfunc1");

	ci_label("y");

	//ci_jmpapentry();
	//ci_jmpsmpcommon();
	//ci_jmpsentinel();
	//ci_jmpuobjep();
	//ci_jmpvuobjretaddr();
	ci_jmpuuobjretaddr();



	//ci_ret();
	//ci_ret32();
	//ci_lret();
	ci_ret64();
}


int subfunc1(void){
	unsigned long long int res;
	res = casm_funccall(15, 16);
}

int main (void)
{
	unsigned long long int result;
	result=casm_funccall(5, 6);
}


//	xmhfhwm_cpu_gprs_esp = xmhfhwm_cpu_gprs_esp + 4;

//result = *((unsigned long int *)xmhfhwm_cpu_gprs_esp+4);


/*typedef int p_func (int *, int);

int main (p_func* func, int *arg1, int arg2)
{
  int result;
s1:
  	//@assert 1;
	//result = (*func)(arg1, arg2);
	result = casm_func(arg1, arg2);

s2:
  return result;
}*/


/*
	 result=((unsigned long long int)(xmhfhwm_cpu_gprs_edx << 32));
*/

/*	result = (
			ci_pushl_esp(0),
			ci_pushl_esp(0),
			ci_pushl_esp(RET_EIP),
			casm_funccall(5, 6),
			ci_popl_esp(0x4),
		    ((unsigned long long int)(xmhfhwm_cpu_gprs_edx << 32) | xmhfhwm_cpu_gprs_eax)
	);*/

/*	(
				ci_pushl_esp(0),
				ci_pushl_esp(0),
				ci_pushl_esp(RET_EIP),
				casm_funccall(5, 6),
				ci_popl_esp(0x4),
			    ((unsigned long long int)(xmhfhwm_cpu_gprs_edx << 32) | xmhfhwm_cpu_gprs_eax)
		);
*/
