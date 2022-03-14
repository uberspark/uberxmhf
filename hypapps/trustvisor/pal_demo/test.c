#include <assert.h>
#include <stdio.h>
#include "vmcall.h"
#include "trustvisor.h"

int main(int argc, char *argv[]) {
	unsigned long eax, result;
	assert(argc > 1);
	assert(sscanf(argv[1], "%lu", &eax) == 1);
	result = vmcall(TV_HC_TEST, eax, 0, 0, 0);
	printf("%lu = vmcall(TV_HC_TEST, %lu)\n", result, eax);
	return (int)result;
}
