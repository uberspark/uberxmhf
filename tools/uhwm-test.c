typedef int p_func (int *, int);

int main (p_func* func, int *arg1, int arg2)
{
  int result;
s1:
  result = (*func)(arg1, arg2);
s2:
  return result;
}
