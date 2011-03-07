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

/*
 *  Intel AMT tcp redirection protocol helper functions.
 *
 *  Copyright (C) 2007 Gerd Hoffmann <kraxel@redhat.com
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include  <fcntl.h>

#include "tcp.h"
#include "redir.h"

static const char *state_name[] = {
    [ REDIR_NONE      ] = "NONE",
    [ REDIR_CONNECT   ] = "CONNECT",
    [ REDIR_INIT      ] = "INIT",
    [ REDIR_AUTH      ] = "AUTH",
    [ REDIR_INIT_SOL  ] = "INIT_SOL",
    [ REDIR_RUN_SOL   ] = "RUN_SOL",
    [ REDIR_INIT_IDER ] = "INIT_IDER",
    [ REDIR_RUN_IDER  ] = "RUN_IDER",
    [ REDIR_CLOSING   ] = "CLOSING",
    [ REDIR_CLOSED    ] = "CLOSED",
    [ REDIR_ERROR     ] = "ERROR",
};

static const char *state_desc[] = {
    [ REDIR_NONE      ] = "disconnected",
    [ REDIR_CONNECT   ] = "connection to host",
    [ REDIR_INIT      ] = "redirection initialization",
    [ REDIR_AUTH      ] = "session authentication",
    [ REDIR_INIT_SOL  ] = "serial-over-lan initialization",
    [ REDIR_RUN_SOL   ] = "serial-over-lan active",
    [ REDIR_INIT_IDER ] = "IDE redirect initialization",
    [ REDIR_RUN_IDER  ] = "IDE redirect active",
    [ REDIR_CLOSING   ] = "redirection shutdown",
    [ REDIR_CLOSED    ] = "connection closed",
    [ REDIR_ERROR     ] = "failure",
};

/* ------------------------------------------------------------------ */

static void hexdump(const char *prefix, const unsigned char *data, size_t size)
{
    char ascii[17];
    int i;

    for (i = 0; i < size; i++) {
	if (0 == (i%16)) {
	    fprintf(stderr,"%s%s%04x:",
		    prefix ? prefix : "",
		    prefix ? ": "   : "",
		    i);
	    memset(ascii,0,sizeof(ascii));
	}
	if (0 == (i%4))
	    fprintf(stderr," ");
	fprintf(stderr," %02x",data[i]);
	ascii[i%16] = isprint(data[i]) ? data[i] : '.';
	if (15 == (i%16))
	    fprintf(stderr,"  %s\n",ascii);
    }
    if (0 != (i%16)) {
	while (0 != (i%16)) {
	    if (0 == (i%4))
		fprintf(stderr," ");
	    fprintf(stderr,"   ");
	    i++;
	};
	fprintf(stderr," %s\n",ascii);
    }
}

static ssize_t redir_write(struct redir *r, const char *buf, size_t count)
{
    int rc;

    if (r->trace)
	hexdump("out", buf, count);
    rc = write(r->sock, buf, count);
    if (-1 == rc)
	snprintf(r->err, sizeof(r->err), "write(socket): %s", strerror(errno));
    return rc;
}

static void redir_state(struct redir *r, enum redir_state new)
{
    enum redir_state old = r->state;

    r->state = new;
    if (r->cb_state)
	r->cb_state(r->cb_data, old, new);
}

/* ------------------------------------------------------------------ */

const char *redir_state_name(enum redir_state state)
{
    const char *name = NULL;

    if (state < sizeof(state_name)/sizeof(state_name[0]))
	name = state_name[state];
    if (NULL == name)
	name = "unknown";
    return name;
}

const char *redir_state_desc(enum redir_state state)
{
    const char *desc = NULL;

    if (state < sizeof(state_desc)/sizeof(state_desc[0]))
	desc = state_desc[state];
    if (NULL == desc)
	desc = "unknown";
    return desc;
}

int redir_connect(struct redir *r)
{
    static unsigned char *defport = "16994";
    struct addrinfo ai;

    memset(&ai, 0, sizeof(ai));
    ai.ai_socktype = SOCK_STREAM;
    ai.ai_family = PF_UNSPEC;
    tcp_verbose = r->verbose;
    redir_state(r, REDIR_CONNECT);
    r->sock = tcp_connect(&ai, NULL, NULL, r->host,
			  strlen(r->port) ? r->port : defport);
    if (-1 == r->sock) {
        redir_state(r, REDIR_ERROR);
        /* FIXME: better error message */
        snprintf(r->err, sizeof(r->err), "connect failed");
	return -1;
    }
    return 0;
}

int redir_start(struct redir *r)
{
    unsigned char request[START_REDIRECTION_SESSION_LENGTH] = {
	START_REDIRECTION_SESSION, 0, 0, 0,  0, 0, 0, 0
    };

    memcpy(request+4, r->type, 4);
    redir_state(r, REDIR_INIT);
    return redir_write(r, request, sizeof(request));
}

int redir_stop(struct redir *r)
{
    unsigned char request[END_REDIRECTION_SESSION_LENGTH] = {
	END_REDIRECTION_SESSION, 0, 0, 0
    };

    redir_state(r, REDIR_CLOSED);
    redir_write(r, request, sizeof(request));
    close(r->sock);
    return 0;
}

int redir_auth(struct redir *r)
{
    int ulen = strlen(r->user);
    int plen = strlen(r->pass);
    int len = 11+ulen+plen;
    int rc;
    unsigned char *request = malloc(len);

    memset(request, 0, len);
    request[0] = AUTHENTICATE_SESSION;
    request[4] = 0x01;
    request[5] = ulen+plen+2;
    request[9] = ulen;
    memcpy(request + 10, r->user, ulen);
    request[10 + ulen] = plen;
    memcpy(request + 11 + ulen, r->pass, plen);
    redir_state(r, REDIR_AUTH);
    rc = redir_write(r, request, len);
    free(request);
    return rc;
}

int redir_sol_start(struct redir *r)
{
    unsigned char request[START_SOL_REDIRECTION_LENGTH] = {
	START_SOL_REDIRECTION, 0, 0, 0,
	0, 0, 0, 0,
	MAX_TRANSMIT_BUFFER & 0xff,
	MAX_TRANSMIT_BUFFER >> 8,
	TRANSMIT_BUFFER_TIMEOUT & 0xff,
	TRANSMIT_BUFFER_TIMEOUT >> 8,
	TRANSMIT_OVERFLOW_TIMEOUT & 0xff,	TRANSMIT_OVERFLOW_TIMEOUT >> 8,
	HOST_SESSION_RX_TIMEOUT & 0xff,
	HOST_SESSION_RX_TIMEOUT >> 8,
	HOST_FIFO_RX_FLUSH_TIMEOUT & 0xff,
	HOST_FIFO_RX_FLUSH_TIMEOUT >> 8,
	HEARTBEAT_INTERVAL & 0xff,
	HEARTBEAT_INTERVAL >> 8,
	0, 0, 0, 0
    };

    redir_state(r, REDIR_INIT_SOL);
    return redir_write(r, request, sizeof(request));
}

int redir_sol_stop(struct redir *r)
{
    unsigned char request[END_SOL_REDIRECTION_LENGTH] = {
	END_SOL_REDIRECTION, 0, 0, 0,
	0, 0, 0, 0,
    };

    redir_state(r, REDIR_CLOSING);
    return redir_write(r, request, sizeof(request));
}

int redir_sol_send(struct redir *r, unsigned char *buf, int blen)
{
    int len = 10+blen;
    int rc;
    unsigned char *request = malloc(len);

    memset(request, 0, len);
    request[0] = SOL_DATA_TO_HOST;
    request[8] = blen & 0xff;
    request[9] = blen >> 8;
    memcpy(request + 10, buf, blen);
    rc = redir_write(r, request, len);
    free(request);
    return rc;
}

int redir_sol_recv(struct redir *r)
{
    unsigned char msg[64];
    int count, len, bshift;
	int flags;

    len = r->buf[8] + (r->buf[9] << 8);
    count = r->blen - 10;
    if (count > len)
	count = len;
    bshift = count + 10;
    if (r->cb_recv)
	r->cb_recv(r->cb_data, r->buf + 10, count);
    len -= count;

    while (len) {
	if (r->trace)
	    fprintf(stderr, "in+: need %d more data bytes\n", len);
	count = sizeof(msg);
	if (count > len)
	    count = len;
	/* temporarily switch to blocking.  the actual data may not be
	 * ready yet, but should be here Real Soon Now. */
	flags = fcntl(r->sock,F_GETFL);
	fcntl(r->sock,F_SETFL, flags & (~O_NONBLOCK));
	count = read(r->sock, msg, count);
	fcntl(r->sock,F_SETFL, flags);

	switch (count) {
	case -1:
	    snprintf(r->err, sizeof(r->err), "read(socket): %s", strerror(errno));
	    return -1;
	case 0:
	    snprintf(r->err, sizeof(r->err), "EOF from socket");
	    return -1;
	default:
	    if (r->trace)
		hexdump("in+", msg, count);
	    if (r->cb_recv)
		r->cb_recv(r->cb_data, msg, count);
	    len -= count;
	}
    }

    return bshift;
}

int redir_data(struct redir *r)
{
    int rc, bshift;

    if (r->trace) {
	fprintf(stderr, "in --\n");
	if (r->blen)
	    fprintf(stderr, "in : already have %d\n", r->blen);
    }
    rc = read(r->sock, r->buf + r->blen, sizeof(r->buf) - r->blen);
    switch (rc) {
    case -1:
	snprintf(r->err, sizeof(r->err), "read(socket): %s", strerror(errno));
	goto err;
    case 0:
	snprintf(r->err, sizeof(r->err), "EOF from socket");
	goto err;
    default:
	if (r->trace)
	    hexdump("in ", r->buf + r->blen, rc);
	r->blen += rc;
    }

    for (;;) {
	if (r->blen < 4)
	    goto again;
	bshift = 0;

	switch (r->buf[0]) {
	case START_REDIRECTION_SESSION_REPLY:
	    bshift = START_REDIRECTION_SESSION_REPLY_LENGTH;
	    if (r->blen < bshift)
		goto again;
	    if (r->buf[1] != STATUS_SUCCESS) {
		snprintf(r->err, sizeof(r->err), "redirection session start failed");
		goto err;
	    }
	    if (-1 == redir_auth(r))
		goto err;
	    break;
	case AUTHENTICATE_SESSION_REPLY:
	    bshift = r->blen; /* FIXME */
	    if (r->blen < bshift)
		goto again;
	    if (r->buf[1] != STATUS_SUCCESS) {
		snprintf(r->err, sizeof(r->err), "session authentication failed");
		goto err;
	    }
	    if (-1 == redir_sol_start(r))
		goto err;
	    break;
	case START_SOL_REDIRECTION_REPLY:
	    bshift = r->blen; /* FIXME */
	    if (r->blen < bshift)
		goto again;
	    if (r->buf[1] != STATUS_SUCCESS) {
		snprintf(r->err, sizeof(r->err), "serial-over-lan redirection failed");
		goto err;
	    }
	    redir_state(r, REDIR_RUN_SOL);
	    break;
	case SOL_HEARTBEAT:
	case SOL_KEEP_ALIVE_PING:
	case IDER_HEARTBEAT:
	case IDER_KEEP_ALIVE_PING:
	    bshift = HEARTBEAT_LENGTH;
	    if (r->blen < bshift)
		goto again;
	    if (HEARTBEAT_LENGTH != redir_write(r, r->buf, HEARTBEAT_LENGTH))
		goto err;
	    break;
	case SOL_DATA_FROM_HOST:
	    if (r->blen < 10) /* header length */
		goto again;
	    bshift = redir_sol_recv(r);
	    if (bshift < 0)
		goto err;
	    break;
	case END_SOL_REDIRECTION_REPLY:
	    bshift = r->blen; /* FIXME */
	    if (r->blen < bshift)
		goto again;
	    redir_stop(r);
	    break;
	default:
	    snprintf(r->err, sizeof(r->err), "%s: unknown r->buf 0x%02x",
		     __FUNCTION__, r->buf[0]);
	    goto err;
	}

	if (bshift == r->blen) {
	    r->blen = 0;
	    break;
	}

	/* have more data, shift by bshift */
	if (r->trace)
	    fprintf(stderr, "in : shift by %d\n", bshift);
	memmove(r->buf, r->buf + bshift, r->blen - bshift);
	r->blen -= bshift;
    }
    return 0;

again:
    /* need more data, jump back into poll/select loop */
    if (r->trace)
	fprintf(stderr, "in : need more data\n");
    return 0;

err:
    if (r->trace)
	fprintf(stderr, "in : ERROR (%s)\n", r->err);
    redir_state(r, REDIR_ERROR);
    close(r->sock);
    return -1;
}
