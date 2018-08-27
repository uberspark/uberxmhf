/*
	logging implementation

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#include <types.h>

#define DEBUG_LOGGING_SERIAL	1


typedef struct {
	u32 hyptask_id;
	u64 timestamp;
	u32 event_type;
} hypmtscheduler_logentry_t;

#define DEBUG_LOG_SIZE (4096/sizeof(hypmtscheduler_logentry_t))


__attribute__((section(".data"))) hypmtscheduler_logentry_t debug_log_buffer[DEBUG_LOG_SIZE];
__attribute__((section(".data"))) u32 debug_log_buffer_index = 0;

void debug_log_tsc(u32 hyptask_id, u64 timestamp, u32 event_type){

	if(debug_log_buffer_index >= DEBUG_LOG_SIZE){
		bcm2837_miniuart_puts("\n[debug_log_tsc]: WARNING: buffer full, not logging anymore!");
	}else{
		debug_log_buffer[debug_log_buffer_index].hyptask_id = hyptask_id;
		debug_log_buffer[debug_log_buffer_index].timestamp = timestamp;
		debug_log_buffer[debug_log_buffer_index].event_type = event_type;

#ifdef DEBUG_LOGGING_SERIAL
		bcm2837_miniuart_puts("\n[debug_log_tsc]: hid=0x");
		debug_hexdumpu32(hyptask_id);
		bcm2837_miniuart_puts(", timestamp=0x");
		debug_hexdumpu32(timestamp >> 32);
		debug_hexdumpu32((u32)timestamp);
		bcm2837_miniuart_puts(", event=0x");
		debug_hexdumpu32(event_type);
#endif

		debug_log_buffer_index++;
	}
}
