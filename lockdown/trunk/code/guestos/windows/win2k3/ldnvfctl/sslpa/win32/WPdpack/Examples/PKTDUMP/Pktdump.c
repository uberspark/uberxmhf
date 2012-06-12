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

#include <stdlib.h>
#include <stdio.h>

#include <pcap.h>

#define MAX_PRINT 80
#define MAX_LINE 16


void dispatcher_handler(u_char *, 
	const struct pcap_pkthdr *, const u_char *);
void usage();

void main(int argc, char **argv) {
pcap_t *fp;
char error[PCAP_ERRBUF_SIZE];

	if (argc < 3)
	{
		printf("\n\t pktdump [-n adapter] | [-f file_name]\n\n");
		return;
	}

	switch (argv[1] [1])
	{
	
	case 'n':
		{
			if ( (fp= pcap_open_live(argv[2], 100, 1, 20, error) ) == NULL)
			{
				fprintf(stderr,"\nError opening adapter\n");
				return;
			}
		};
		break;

	case 'f':
		{
			if ( (fp = pcap_open_offline(argv[2], NULL) ) == NULL)
			{
				fprintf(stderr,"\nError opening dump file\n");
				return;
			}
		};
		break;
	}
		
	// read and dispatch packets until EOF is reached
	pcap_loop(fp, 0, dispatcher_handler, NULL);
	
}



void dispatcher_handler(u_char *temp1, 
	const struct pcap_pkthdr *header, const u_char *pkt_data)
{
u_int i=0;
	
	//print pkt timestamp and pkt len
	printf("%ld:%ld (%ld)\n", header->ts.tv_sec, header->ts.tv_usec, header->len);			
	

	while ( (i<MAX_PRINT) && (i<header->len) )
	{
		i++;
		printf("%x ", pkt_data[i-1]);
		if ( (i%MAX_LINE) == 0) printf("\n");
	}
	
	printf("\n\n");

}


void usage()
{
	
	printf("\n\t pktdump [-n adapter] | [-f file_name]\n");
	exit(0);
}