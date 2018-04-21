/*
*
@file		sockutil.c
@brief	Implementation of useful function of iinChip
*
*/


#include <stdio.h>
#include <string.h>

#include "include_netif/types.h"
#include "include_netif/sockutil.h"

uint16 swaps(u_int i);
uint32 swapl(uint32 l);

uint16 swaps(u_int i)
{
	u_short ret=0;
	ret = (i & 0xFF) << 8;
	ret |= ((i >> 8)& 0xFF);
	return ret;	
}

uint32 swapl(uint32 l)
{
	u_long ret=0;
	ret = (l & 0xFF) << 24;
	ret |= ((l >> 8) & 0xFF) << 16;
	ret |= ((l >> 16) & 0xFF) << 8;
	ret |= ((l >> 24) & 0xFF);
	return ret;
}


/**
@brief	Convert 32bit Address(Host Ordering) into Dotted Decimal Format
@return 	a char pointer to a static buffer containing the text address in standard ".'' notation. Otherwise, it returns NULL. 
*/  
char* inet_ntoa(
	unsigned long addr	/**< Pointer variable to store converted value(INPUT) */
	)
{
	static char addr_str[16];
	memset(addr_str,0,16);
	sprintf(addr_str,"%d.%d.%d.%d",(int)(addr>>24 & 0xFF),(int)(addr>>16 & 0xFF),(int)(addr>>8 & 0xFF),(int)(addr & 0xFF));
	return addr_str;
}

#if 0
char* inet_ntoa_pad(unsigned long addr)
{
	static char addr_str[16];
	memset(addr_str,0,16);
	sprintf(addr_str,"%03d.%03d.%03d.%03d",(int)(addr>>24 & 0xFF),(int)(addr>>16 & 0xFF),(int)(addr>>8 & 0xFF),(int)(addr & 0xFF));
	return addr_str;
}

/**
@brief	Converts a string containing an (Ipv4) Internet Protocol decimal dotted address into a 32bit address 
@return 	32bit address (Host Odering)
*/  
uint32 inet_addr(
	unsigned char* addr	/**< dotted notation address string.  */
	)
{
	char i;
	uint32 inetaddr = 0;
	char taddr[30];
	char * nexttok;
	int num;
	strcpy(taddr,addr);
	
	nexttok = taddr;
	for(i = 0; i < 4 ; i++)
	{
		nexttok = strtok(nexttok,".");
		if(nexttok[0] == '0' && nexttok[1] == 'x') num = ATOI(nexttok+2,0x10);
		else num = ATOI(nexttok,10);
		inetaddr = inetaddr << 8;		
		inetaddr |= (num & 0xFF);
		nexttok = NULL;
	}
	return inetaddr;	
}	


/**
@brief	Verify dotted notation IP address string
@return 	success - 1, fail - 0
*/ 
char VerifyIPAddress(
	char* src	/**< pointer to IP address string */
	)
{
	int i;
	int tnum;
	char tsrc[50];
	char* tok = tsrc;
	
	strcpy(tsrc,src);
	
	for(i = 0; i < 4; i++)
	{
		tok = strtok(tok,".");
		if ( !tok ) return 0;
		if(tok[0] == '0' && tok[1] == 'x')
		{
			if(!ValidATOI(tok+2,0x10,&tnum)) return 0;
		}
		else if(!ValidATOI(tok,10,&tnum)) return 0;
		
		if(tnum < 0 || tnum > 255) return 0;
		tok = NULL;
	}
	return 1;	
}


/**
@brief	Output destination IP address of appropriate channel
@return 	32bit destination address (Host Ordering)
*/ 
uint32 GetDestAddr(
	SOCKET s	/**< Channel number which try to get destination IP Address */
	)
{
	uint32 addr=0;
	int i = 0;
	for(i=0; i < 4; i++)
	{
		addr <<=8;
		addr += IINCHIP_READ(Sn_DIPR0(s)+i);
	}
	return addr;
}

/**
@brief	Output destination port number of appropriate channel
@return 	16bit destination port number
*/ 
unsigned int GetDestPort(
	SOCKET s	/**< Channel number which try to get destination port */
	)
{
	u_int port;
	port = ((u_int) IINCHIP_READ(Sn_DPORT0(s))) & 0x00FF;
	port <<= 8;
	port += ((u_int) IINCHIP_READ(Sn_DPORT0(s)+1)) & 0x00FF;
	return port;
}
#endif

/**
@brief	htons function converts a unsigned short from host to TCP/IP network byte order (which is big-endian).
@return 	the value in TCP/IP network byte order
*/ 
uint16 htons( uint16 hostshort )	/**< A 16-bit number in host byte order.  */
{
	return swaps(hostshort);
}


/**
@brief	htonl function converts a unsigned long from host to TCP/IP network byte order (which is big-endian).
@return 	the value in TCP/IP network byte order
*/ 
uint32 htonl( uint32 hostlong )		/**< hostshort  - A 32-bit number in host byte order.  */
{
	return swapl(hostlong);
}


/**
@brief	ntohs function converts a unsigned short from TCP/IP network byte order to host byte order (which is little-endian on Intel processors).
@return 	a 16-bit number in host byte order
*/ 
unsigned long ntohs( 	unsigned short netshort )	/**< netshort - network odering 16bit value */
{
	return htons(netshort);
}


/**
@brief	converts a unsigned long from TCP/IP network byte order to host byte order (which is little-endian on Intel processors).
@return 	a 16-bit number in host byte order
*/ 
unsigned long ntohl(unsigned long netlong)
{
	return htonl(netlong);
}

#if 0
// destip : BigEndian
u_char CheckDestInLocal(u_long destip)
{
	int i = 0;
	u_char * pdestip = (u_char*)&destip;
	for(i =0; i < 4; i++)
	{
		if((pdestip[i] & IINCHIP_READ(SUBR0+i)) != (IINCHIP_READ(SIPR0+i) & IINCHIP_READ(SUBR0+i)))
			return 1;	// Remote
	}
	return 0;
}


/**
@brief	Get handle of socket which status is same to 'status'
@return 	socket number
*/ 
SOCKET getSocket(
	unsigned char status, 	/**< socket's status to be found */
	SOCKET start			/**< base of socket to be found */
	)
{
	SOCKET i;
	if(start > 3) start = 0;

	for(i = start; i < MAX_SOCK_NUM ; i++) if( getSn_SR(i)==status ) return i;
	return MAX_SOCK_NUM;	
}


/**
@brief	Calculate checksum of a stream
@return 	checksum
*/ 
unsigned short checksum(
	unsigned char * src, 	/**< pointer to stream  */
	unsigned int len		/**< size of stream */
	)
{
	u_int sum, tsum, i, j;
	u_long lsum;

	j = len >> 1;

	lsum = 0;

	for (i = 0; i < j; i++) 
	{
		tsum = src[i * 2];
		tsum = tsum << 8;
		tsum += src[i * 2 + 1];
		lsum += tsum;
	}

	if (len % 2) 
	{
		tsum = src[i * 2];
		lsum += (tsum << 8);
	}


	sum = lsum;
	sum = ~(sum + (lsum >> 16));
	return (u_short) sum;	
}



#ifndef NO_USE_SOCKUTIL_FUNC
/**
@brief	Get Source IP Address of iinChip.
@return 	Source IP Address(32bit Address-Host Ordering)
*/ 
u_long GetIPAddress(void)
{
	u_long ip=0;
	int i;
	for(i=0; i < 4; i++)
	{
		ip <<= 8;
		ip += (char)IINCHIP_READ(SIPR0+i);
	}
	return ip;
}


/**
@brief	Get Gateway IP Address of iinChip.
@return 	Gateway IP Address(32bit Address-Host Ordering)
*/ 
u_long GetGWAddress(void)
{
	u_long ip=0;
	int i;
	for(i=0; i < 4; i++)
	{
		ip <<= 8;
		ip += (char)IINCHIP_READ(GAR0+i);
	}
	return ip;	
}


/**
@brief	Get Subnet mask of iinChip.
@return 	Subnet Mask(32bit Address-Host Ordering)
*/ 
u_long GetSubMask(void)
{
	u_long ip=0;
	int i;
	for(i=0; i < 4; i++)
	{
		ip <<= 8;
		ip += (char)IINCHIP_READ(SUBR0+i);
	}
	return ip;	
}


/**
@brief	Get Mac Address of iinChip.
@return 	Subnet Mask(32bit Address-Host Ordering)
*/ 
void GetMacAddress(
	unsigned char* mac	/**< Pointer to store Mac Address(48bit Address)(INPUT, OUTPUT) */
	)
{
	int i = 0;
	for(i=0; i<6;i++)*mac++ = IINCHIP_READ(SHAR0+i);
}

void GetDestMacAddr(SOCKET s, u_char* mac)
{
	int i = 0;
	for(i=0; i<6;i++)*mac++ = IINCHIP_READ(Sn_DHAR0(s)+i);
}


/**
@brief	Read established network information(G/W, IP, S/N, Mac) of iinChip and Output that through Serial.
		Mac Address is output into format of Dotted HexaDecimal.Others are output into format of Dotted Decimal Format.
*/ 
void GetNetConfig(void)
{
	u_char addr[6];
	u_long iaddr;
	printf("\r\n================================================\r\n");
	printf("       Net Config Information\r\n");
	printf("================================================\r\n");
	GetMacAddress(addr);
	printf("MAC ADDRESS      : 0x%02X.0x%02X.0x%02X.0x%02X.0x%02X.0x%02X\r\n",addr[0],addr[1],addr[2],addr[3],addr[4],addr[5]);
	
	iaddr = GetSubMask();
	printf("SUBNET MASK      : %s\r\n",inet_ntoa(iaddr));

	iaddr = GetGWAddress();
	printf("G/W IP ADDRESS   : %s\r\n",inet_ntoa(iaddr));

	iaddr = GetIPAddress();
	printf("LOCAL IP ADDRESS : %s\r\n",inet_ntoa(iaddr));
	printf("================================================\r\n");		
}

#endif
#endif
