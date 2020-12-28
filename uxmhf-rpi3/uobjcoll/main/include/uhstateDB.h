#ifndef __UHSTATEDB_H__
#define __UHSTATEDB_H__

#define UAPP_UHSTATEDB_FUNCTION_INIT    0x60
#define UAPP_UHSTATEDB_FUNCTION_GET     0x61
#define UAPP_UHSTATEDB_FUNCTION_NEXT    0x62

#define MAX_STATES 10

#ifndef __ASSEMBLY__

typedef struct {
  uint32_t maxArray[MAX_STATES];
  uint32_t numStates;
  uint32_t vaddr;
  uint32_t deviceID;  
  int32_t stateVal;
}uhstatedb_param_t;


#endif // __ASSEMBLY__

#endif // __UHSTATEDB_H__
