#ifndef __UAGENT_H__
#define __UAGENT_H__

#define UAPP_UAGENT_FUNCTION_SIGN    0x67
#define MAX_SIZE 1600

#ifndef __ASSEMBLY__

typedef struct {
  uint8_t pkt_data[MAX_SIZE];
  uint32_t pkt_size;
  uint32_t vaddr;
  uint32_t op;
}uagent_param_t;


#endif // __ASSEMBLY__

#endif // __UAGENT_H__
