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
#define RET_EIP 0xabcd0000

extern unsigned int xmhfhwm_cpu_gprs_edx, xmhfhwm_cpu_gprs_eax;


int main (void)
{
	int result;

	casm_funccall(5, 6);

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

}

