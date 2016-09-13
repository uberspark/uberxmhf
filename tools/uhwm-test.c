typedef int p_func (int *, int);

int main (p_func* func, int *arg1, int arg2)
{
  int result;
s1:
  	//@assert 1;
	//result = (*func)(arg1, arg2);
	result = casm_func(arg1, arg2);

s2:
  return result;
}
