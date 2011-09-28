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
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
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

#include "audit.h"

int audit_ctx_init(audit_ctx_t *ctx, const char* hostname, const char* svc)
{
  ctx->hostname = hostname;
  ctx->svc = svc;
  return 0;
}

void audit_ctx_release(audit_ctx_t *ctx)
{
}

static int audit_connect(audit_ctx_t* audit_ctx, int *sock)
{
  int status=0;
  struct addrinfo *servinfo;  // will point to the results

  {
    struct addrinfo hints;
    memset(&hints, 0, sizeof hints); // make sure the struct is empty
    hints.ai_family = AF_UNSPEC;     // don't care IPv4 or IPv6
    hints.ai_socktype = SOCK_STREAM; // TCP stream sockets

    // get ready to connect
    status = getaddrinfo(audit_ctx->hostname, audit_ctx->svc, &hints, &servinfo);
    if(status) {
      status = AUDIT_ELOOKUP;
      goto out;
    }
  }

  {
    *sock = socket(servinfo->ai_family, servinfo->ai_socktype, servinfo->ai_protocol);
    if(*sock < 0) {
      status = AUDIT_ESOCK;
      goto free_addr;
    }
  }

  {
    status = connect(*sock, servinfo->ai_addr, servinfo->ai_addrlen);
    if(status) {
      status = AUDIT_ECONNECT;
      close(*sock);
      goto free_addr;
    }
  }

 free_addr:
  freeaddrinfo(servinfo);
 out:
  return status;
}

static int sendall(int s, const void *buf, size_t len)
{
  int total = 0;        // how many bytes we've sent
  int bytesleft = len; // how many we have left to send
  int n;

  while(total < len) {
    n = send(s, buf+total, bytesleft, 0);
    if (n == -1) { break; }
    total += n;
    bytesleft -= n;
  }

  return n==-1?-1:0; // return -1 on failure, 0 on success
} 

static int recvall(int s, void *buf, size_t len)
{
  int total = 0;        // how many bytes we've recvd
  int bytesleft = len; // how many we have left to recv
  int n;

  while(total < len) {
    n = recv(s, buf+total, bytesleft, 0);
    if (n == -1) { break; }
    total += n;
    bytesleft -= n;
  }

  return n==-1?-1:0; // return -1 on failure, 0 on success
} 


int audit_get_token(audit_ctx_t*    audit_ctx,
                    const uint8_t*  audit_nonce,
                    size_t          audit_nonce_len,
                    const char*     audit_string,
                    size_t          audit_string_len,
                    void*           audit_token,
                    size_t*         audit_token_len)
{
  int sock;
  int status=0;
  uint32_t tmp_ui32;

  status = audit_connect(audit_ctx, &sock);
  if(status) {
    return status;
  }

  tmp_ui32 = htonl(audit_nonce_len);
  if (sendall(sock, &tmp_ui32, sizeof(tmp_ui32))
      || sendall(sock, audit_nonce, audit_nonce_len)) {
    status = AUDIT_ESEND;
    goto close_sock;
  }

  tmp_ui32 = htonl(audit_string_len);
  if (sendall(sock, &tmp_ui32, sizeof(tmp_ui32))
      || sendall(sock, audit_string, audit_string_len)) {
    status = AUDIT_ESEND;
    goto close_sock;
  }

  if(recvall(sock, &tmp_ui32, sizeof(tmp_ui32))) {
    status = AUDIT_ERECV;
    goto close_sock;
  }
  tmp_ui32 = ntohl(tmp_ui32);
  if(tmp_ui32 > *audit_token_len) {
    *audit_token_len = tmp_ui32;
    status = AUDIT_ESHORT_BUFFER;
    goto close_sock;
  }
  *audit_token_len = tmp_ui32;
  if(recvall(sock, audit_token, tmp_ui32)) {
    status = AUDIT_ERECV;
    goto close_sock;
  }

 close_sock:
  close(sock);
  return status;
}
