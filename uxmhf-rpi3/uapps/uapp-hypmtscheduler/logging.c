/*
	logging implementation

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>

#define PRIORITY_QUEUE_SIZE 5

typedef struct {
	u32 hyptask_id;
	u64 timestamp;
	u32 event_type;
} hypmtscheduler_logentry_t;

