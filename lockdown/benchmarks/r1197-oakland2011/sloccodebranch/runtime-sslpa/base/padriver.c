//padriver.c
//SSL protocol driver for lockdown
//author(s): amit vasudevan (amitvasudevan@acm.org)

#include <lockdown/types.h>
#include <lockdown/lockdown.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <net/if.h>
#include <netinet/if_ether.h>

#include "network.h"
#include <r_common.h>
#include <r_time.h>
#include "ssl_analyze.h"

#ifndef ETHERTYPE_8021Q
#define ETHERTYPE_8021Q 0x8100
#endif

typedef struct module_def_ {
     char *name;
     proto_mod *mod;
} module_def;

static module_def modules[]={
     {"SSL",&ssl_mod},
     {0,0}
};


int parse_ssl_flag PROTO_LIST((int c));

//the protocol handler (ssl)
n_handler *n;

//------------------------------------------------------------------------------
//initialize ssl pa
//returns 0 on failure, 1 on success
int ssl_pa_init(){
    proto_mod *mod=&ssl_mod;
    int r;

    if(r=network_handler_create(mod,&n)){
			printf("sslpa: could not create network handler: %d\n", r);
			return 0;
		}

		return 1;
}
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
//high level pa function to analyze a particular packet. it expects a 
//packet and its length
void ssl_pa_analyze(u8 *packet, u32 packet_len){
    int len;
    struct ether_header *e_hdr=(struct ether_header *)packet;
    int type;
		struct timeval ts;
    len=packet_len;
    
    type=ntohs(e_hdr->ether_type);

    packet+=sizeof(struct ether_header);
    len-=sizeof(struct ether_header);

	  /* if vlans, push past VLAN header (4 bytes) */
    if(type==ETHERTYPE_8021Q) {
    	type=ntohs(*(u_int16_t *)(packet + 2));

      packet+=4;
      len+=4;
    }

    if(type!=ETHERTYPE_IP)	
      return;								//TODO: check for DNS udp packet and if not DROP!
        
    //setup a dummy timestamp
    ts.tv_sec = 0;
    ts.tv_usec= 0;
 
 		//hand the packet off for analysis   
    network_process_packet(n, &ts , packet ,len);
}
//------------------------------------------------------------------------------


