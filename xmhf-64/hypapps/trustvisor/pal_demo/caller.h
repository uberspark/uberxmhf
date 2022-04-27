#include "trustvisor.h"

void *register_pal(struct tv_pal_params *params, void *entry, void *begin_pal,
					void *end_pal, int verbose);
void unregister_pal(void *reloc_entry);
