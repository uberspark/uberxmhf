/*
 * frama-c coding conformance plugin test file
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
extern unsigned int ext_var1;
int myfunc_ptrfunc(int a);

//unsigned char xmhfhwm_buf[512];
unsigned char buf[512];
int glob_a=5, glob_b;
int (*ptr_myfunc_ptrfunc)(int a) = myfunc_ptrfunc;

void myfunc(int a, int b);


/*

int xmhfhwm_myfunc_notused(int a, int b, int c){
	int d=0;
	d = a + b - c;
	d += b;
	return d;
}
*/

int myfunc_ptrfunc(int a){
	int b=0;
	b = a + 7;
	return b;
}

static void myfunc_static(void){
	puts("this is just a static function \n");
}

void myfunc(int a, int b){
	buf[a+b] = 'A';
	a = a+b;
	b = b-a;
	if(a > b)
		printf("a=%u, b=%u\n", a, b);
	else
		printf("b=%u, a=%u\n", b, a);

	//a = myfunc_ptrfunc(b);
	a = ptr_myfunc_ptrfunc(b);
}

