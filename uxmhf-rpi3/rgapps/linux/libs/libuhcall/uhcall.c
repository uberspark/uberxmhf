/*
 * uhcall -- guest interface for micro hypervisor hypercall
 *
 * author: amit vasudevan (amitvasudevan@acm.org)
 */

#include<stdio.h>
#include<stdlib.h>
#include<errno.h>
#include<fcntl.h>
#include<string.h>
#include<unistd.h>
#include <sys/mman.h>
