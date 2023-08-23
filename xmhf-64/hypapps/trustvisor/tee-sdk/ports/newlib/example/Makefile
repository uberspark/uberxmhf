NEWLIB=../install/i586

all:
	gcc -g -nostdlib -static -I $(NEWLIB)/include -L $(NEWLIB)/lib -o hello crt0.s hello.c -lc -lnosys -lg -lm -lgcc
