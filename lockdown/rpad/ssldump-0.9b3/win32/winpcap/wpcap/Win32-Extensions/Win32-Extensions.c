/*
 * Copyright (c) 1999, 2000
 *	Politecnico di Torino.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that: (1) source code distributions
 * retain the above copyright notice and this paragraph in its entirety, (2)
 * distributions including binary code include the above copyright notice and
 * this paragraph in its entirety in the documentation or other materials
 * provided with the distribution, and (3) all advertising materials mentioning
 * features or use of this software display the following acknowledgement:
 * ``This product includes software developed by the Politecnico
 * di Torino, and its contributors.'' Neither the name of
 * the University nor the names of its contributors may be used to endorse
 * or promote products derived from this software without specific prior
 * written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 */

#include "pcap-int.h"
#include <packet32.h>

/*set the driver's working mode*/
int 
pcap_setmode(pcap_t *p, int mode){
	
	if (p->adapter==NULL)
	{
		sprintf(p->errbuf, "impossible to set mode while reading from a file");
		return -1;
	}

	if(PacketSetMode(p->adapter,mode)==FALSE)
	{
		sprintf(p->errbuf, "driver error: working mode not recognized");
		return -1;
	}

	return 0;
}

/*send a packet to the network*/
int 
pcap_sendpacket(pcap_t *p, u_char *buf, int size){
	LPPACKET PacketToSend;

	if (p->adapter==NULL)
	{
		sprintf(p->errbuf, "Writing a packet is allowed only on a physical adapter");
		return -1;
	}

	PacketToSend=PacketAllocatePacket();
	PacketInitPacket(PacketToSend,buf,size);
	if(PacketSendPacket(p->adapter,PacketToSend,TRUE)==FALSE){
		PacketFreePacket(PacketToSend);
		return -1;
	}

	PacketFreePacket(PacketToSend);
	return 0;
}

/*set the dimension of the kernel capture buffer*/
int 
pcap_setbuff(pcap_t *p, int dim)
{
	if (p->adapter==NULL)
	{
		sprintf(p->errbuf, "The buffer size cannot be set while reading from a file");
		return -1;
	}
	
	if(PacketSetBuff(p->adapter,dim)==FALSE)
	{
		sprintf(p->errbuf, "driver error: not enough memory to allocate the buffer");
		return -1;
	}
	return 0;
}

/*returns the handle to the read event associated with the adapter*/
HANDLE
pcap_getevent(pcap_t *p)
{
	if (p->adapter==NULL)
	{
		sprintf(p->errbuf, "The read event cannot be retrieved while reading from a file");
		return NULL;
	}	

	return p->adapter->ReadEvent;

}

/*set the minimum amount of data that will release a read call*/
int 
pcap_setmintocopy(pcap_t *p, int size)
{
	if (p->adapter==NULL)
	{
		sprintf(p->errbuf, "Inpossible to set the mintocopy parameter on an offline capture");
		return -1;
	}	

	if(PacketSetMinToCopy(p->adapter, size)==FALSE)
	{
		sprintf(p->errbuf, "driver error: unable to set the read block size");
		return -1;
	}
	return 0;
}
