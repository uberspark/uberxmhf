/* from http://wiki.osdev.org/Porting_Newlib */

        .global _start
        .extern main

_start:

        ## here you might want to get the argc/argv pairs somehow and then push
        ## them onto the stack...

        # call the user's function
        call main

        # call linux's exit system call with main's return value
        movl %eax,%ebx
        movl $1,%eax
        int $0x80
