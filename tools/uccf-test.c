/*
 * frama-c coding conformance plugin test file
 * author: amit vasudevan (amitvasudevan@acm.org)
 */
extern unsigned int ext_var1;

int glob_a, glob_b;

void myfunc(int a, int b){
	printf("a=%u, b=%u\n", a, b);
}

