/*
 * frama-c coding conformance plugin test file
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
extern unsigned int ext_var1;

int glob_a=5, glob_b;

void myfunc(int a, int b);

static void myfunc_static(void){
	puts("this is just a static function \n");
}

void myfunc(int a, int b){
	a = a+b;
	b = b-a;
	if(a > b)
		printf("a=%u, b=%u\n", a, b);
	else
		printf("b=%u, a=%u\n", b, a);

}

