#define RET_EIP 0xabcd0000

extern unsigned int xmhfhwm_cpu_gprs_edx, xmhfhwm_cpu_gprs_eax;
extern void ci_pushl(unsigned int);
extern unsigned long long casm_funccall(unsigned int x, unsigned int y);

unsigned long long casm_funkyfunc(unsigned int x, unsigned int y){
	ci_ret(x+y);
	ci_label("x:");

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
