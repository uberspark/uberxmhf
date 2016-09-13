typedef int p_func (int *, int);

int main (p_func* func, int *arg1, int arg2)
{
  int result;
  
  result = (*func)(arg1, arg2);
  return result;
}