/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

#include <stddef.h>
#include <string.h>
#include <unistd.h>

#ifdef WIN32
#define _WIN32_WINNT 0x0501
#include <winsock2.h>
#include <ws2tcpip.h>
#else
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#endif

#include "dbg.h"
#include "audit.h"

audit_err_t audit_ctx_init(audit_ctx_t *ctx,
 const char* hostname, const char* svc)
{
  audit_err_t rv=0;
  ctx->hostname = hostname;
  ctx->svc = svc;

#ifdef WIN32
  {
    WORD wVersionRequested;
    WSADATA wsaData;

    /* Use the MAKEWORD(lowbyte, highbyte) macro declared in Windef.h */
    wVersionRequested = MAKEWORD(2, 2);

    rv = WSAStartup(wVersionRequested, &wsaData);
    CHECK_RV( rv, AUDIT_ESYSTEM, "WSAStartup");

    /* Confirm that the WinSock DLL supports 2.2.*/
    /* Note that if the DLL supports versions greater    */
    /* than 2.2 in addition to 2.2, it will still return */
    /* 2.2 in wVersion since that is the version we      */
    /* requested.                                        */

    if (LOBYTE(wsaData.wVersion) != 2 || HIBYTE(wsaData.wVersion) != 2) {
      /* Tell the user that we could not find a usable */
      /* WinSock DLL.                                  */
      log_err( "Could not find a usable version of Winsock.dll");
      WSACleanup();
      rv = AUDIT_ESYSTEM;
      goto out;
    }
  }
#endif

 out:
  return rv;
}

void audit_ctx_release(audit_ctx_t *ctx)
{
#ifdef WIN32
  WSACleanup();
#endif
}

static audit_err_t audit_connect(audit_ctx_t* audit_ctx, int *sock)
{
  audit_err_t rv=0;
  int err;
  struct addrinfo *servinfo, *servinfo_list=NULL;  // will point to the results

  *sock=-1;

  {
    struct addrinfo hints;
    memset(&hints, 0, sizeof hints); // make sure the struct is empty
    hints.ai_family = AF_UNSPEC;     // don't care IPv4 or IPv6
    hints.ai_socktype = SOCK_STREAM; // TCP stream sockets

    // get ready to connect
    err = getaddrinfo(audit_ctx->hostname, audit_ctx->svc, &hints, &servinfo_list);
    CHECK_RV(err, AUDIT_ELOOKUP, "getaddrinfo(%s)", audit_ctx->hostname);
  }

  servinfo=servinfo_list;
  for(servinfo=servinfo_list; servinfo; servinfo = servinfo->ai_next) {
    *sock = socket(servinfo->ai_family, servinfo->ai_socktype, servinfo->ai_protocol);
    CHECK(*sock >= 0, AUDIT_ESOCK, "socket()");

    err = connect(*sock, servinfo->ai_addr, servinfo->ai_addrlen);
    if (err) {
      close(*sock);
      *sock=-1;
    }
  }
  CHECK(*sock >= 0,
        AUDIT_ECONNECT, "couldn't connect to (%s:%s)",
        audit_ctx->hostname,
        audit_ctx->svc);

 out:
  if(servinfo) {
    freeaddrinfo(servinfo_list);
    servinfo=NULL;
  }
  if(rv && *sock >= 0) {
    close(*sock);
    *sock=-1;
  }
  return rv;
}

static int sendall(int s, const void *buf, size_t len)
{
  int total = 0;        // how many bytes we've sent
  int bytesleft = len; // how many we have left to send
  int n;
  int rv=0;

  while(total < len) {
    n = send(s, buf+total, bytesleft, 0);
    CHECK(n>=0, -1, "send");
    total += n;
    bytesleft -= n;
  }

 out:
  return rv;
} 

static int recvall(int s, void *buf, size_t len)
{
  int total = 0;        // how many bytes we've recvd
  int bytesleft = len; // how many we have left to recv
  int n;
  int rv=0;

  while(total < len) {
    n = recv(s, buf+total, bytesleft, 0);
    CHECK(n>=0, -1, "recv");
    total += n;
    bytesleft -= n;
  }

 out:
  if (rv) {
    return rv;
  }
  return n==-1?-1:0; // return -1 on failure, 0 on success
} 


audit_err_t audit_get_token(audit_ctx_t*    audit_ctx,
                            const uint8_t*  audit_nonce,
                            size_t          audit_nonce_len,
                            const char*     audit_string,
                            size_t          audit_string_len,
                            void*           audit_token,
                            size_t*         audit_token_len)
{
  int sock=-1;
  uint32_t tmp_ui32;
  audit_err_t rv=0;

  rv = audit_connect(audit_ctx, &sock);
  CHECK_RV(rv, rv, "audit_connect");

  tmp_ui32 = htonl(audit_nonce_len);
  rv = sendall(sock, &tmp_ui32, sizeof(tmp_ui32));
  CHECK_RV(rv, AUDIT_ESEND, "sendall");
  rv = sendall(sock, audit_nonce, audit_nonce_len);
  CHECK_RV(rv, AUDIT_ESEND, "sendall");

  tmp_ui32 = htonl(audit_string_len);
  rv = sendall(sock, &tmp_ui32, sizeof(tmp_ui32));
  CHECK_RV(rv, AUDIT_ESEND, "sendall");
  rv = sendall(sock, audit_string, audit_string_len);
  CHECK_RV(rv, AUDIT_ESEND, "sendall");

  rv = recvall(sock, &tmp_ui32, sizeof(tmp_ui32));
  CHECK_RV(rv, AUDIT_ERECV, "recvall");

  tmp_ui32 = ntohl(tmp_ui32);
  if(tmp_ui32 > *audit_token_len) {
    *audit_token_len = tmp_ui32;
    rv = AUDIT_ESHORT_BUFFER;
    goto out;
  }

  *audit_token_len = tmp_ui32;
  rv = recvall(sock, audit_token, tmp_ui32);
  CHECK_RV(rv, AUDIT_ERECV, "recvall");

 out:
  if(sock >= 0) {
    close(sock);
    sock=-1;
  }
  return rv;
}
