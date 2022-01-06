#include "pal.h"

void begin_pal_c() {}

unsigned long my_pal(unsigned long arg1, unsigned long *arg2) {
	return arg1 + ((*arg2)++);
}

void end_pal_c() {}
