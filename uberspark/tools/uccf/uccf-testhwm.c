/*
 * frama-c coding conformance plugin test file
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

int xmhfhwm_myfunc_ptrfunc(int a);

unsigned char xmhfhwm_buf[512];
//unsigned char buf[512];
int xmhfhwm_glob_a=5, xmhfhwm_glob_b;
int (*xmhfhwm_ptr_myfunc_ptrfunc)(int a) = xmhfhwm_myfunc_ptrfunc;

int xmhfhwm_myfunc_ptrfunc(int a){
	int b=0;
	b = a + 7;
	return b;
}

static void xmhfhwm_myfunc_static(void){
	xmhfhwm_puts("this is just a static function \n");
}

void xmhfhwm_myfunc(int a, int b){
	xmhfhwm_buf[a+b] = 'A';
	a = a+b;
	b = b-a;
	if(a > b)
		xmhfhwm_printf("a=%u, b=%u\n", a, b);
	else
		xmhfhwm_printf("b=%u, a=%u\n", b, a);

	//a = myfunc_ptrfunc(b);
	a = xmhfhwm_ptr_myfunc_ptrfunc(b);
}

