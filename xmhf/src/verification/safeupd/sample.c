#include <stdio.h>
#include <stdlib.h>


extern void myfunc(int x);

char a[50];
char *p;
unsigned int addrp;
main(){
		a[1]='A';
		p=&a[1];
		addrp=(unsigned int)p;
		printf("\naddress of p=%x", addrp);

		myfunc(3);

		*p='B';
		addrp= (unsigned int)&(*p);
		printf("\naddress of p=%x", addrp);
		printf("\n%c\n", a[1]);
}
