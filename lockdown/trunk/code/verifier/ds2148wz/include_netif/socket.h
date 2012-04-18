#ifndef	_SOCKET_H_
#define	_SOCKET_H_

/**
 * \file    socket.h
 * WIZnet SOCKET API function definition
 *
 * For user application, WIZnet provides SOCKET API functions 
 * which are similar to Berkeley SOCKET API.\n
 *
 * \author MidnightCow
 * \date 24/03/2008
 * \version 1.0.0
 *
 * Release with W5300 launching
 *
 */
#include "types.h"
#include "w5300.h"

/**********************************
 * define function of SOCKET APIs * 
 **********************************/

/**
 * Open a SOCKET.
 */ 
uint8    socket(SOCKET s, uint8 protocol, uint16 port, uint16 flag);

/**
 * Close a SOCKET.
 */ 
void     close(SOCKET s);                                                           // Close socket

/**
 * It tries to connect a client.
 */
uint8    connect(SOCKET s, uint8 * addr, uint16 port);

/**
 * It tries to disconnect a connection SOCKET with a peer.
 */
void     disconnect(SOCKET s); 

/**
 * It is listening to a connect-request from a client.
 */
uint8    listen(SOCKET s);	    


/**
 * It receives TCP data on a connection SOCKET
 */
uint32   recv(SOCKET s, uint8 * buf, uint32 len);

#endif
/* _SOCKET_H_ */

