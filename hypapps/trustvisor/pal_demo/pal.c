#include "pal.h"

void start_pal_c() {}

int my_pal(uint32_t arg1, uint32_t *arg2) {
	return arg1 + *arg2;
}

void end_pal_c() {}
