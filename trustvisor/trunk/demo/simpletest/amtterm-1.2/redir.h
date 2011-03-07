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

#include "RedirectionConstants.h"

enum redir_state {
    REDIR_NONE      =  0,
    REDIR_CONNECT   =  1,
    REDIR_INIT      =  2,
    REDIR_AUTH      =  3,
    REDIR_INIT_SOL  = 10,
    REDIR_RUN_SOL   = 11,
    REDIR_INIT_IDER = 20,
    REDIR_RUN_IDER  = 21,
    REDIR_CLOSING   = 30,
    REDIR_CLOSED    = 31,
    REDIR_ERROR     = 40,
};

struct redir {
    /* host connection */
    unsigned char     host[64];
    unsigned char     port[16];
    unsigned char     user[16];
    unsigned char     pass[16];

    /* serial-over-lan */
    unsigned char     type[4];
    int               verbose;
    int               trace;
    enum redir_state  state;
    unsigned char     err[128]; // state == REDIR_ERROR

    int               sock;
    unsigned char     buf[64];
    unsigned int      blen;

    /* callbacks */
    void *cb_data;
    void (*cb_state)(void *cb_data, enum redir_state old, enum redir_state new);
    int (*cb_recv)(void *cb_data, unsigned char *buf, int len);
};

const char *redir_state_name(enum redir_state state);
const char *redir_state_desc(enum redir_state state);

int redir_connect(struct redir *r);
int redir_start(struct redir *r);
int redir_stop(struct redir *r);
int redir_auth(struct redir *r);
int redir_sol_start(struct redir *r);
int redir_sol_stop(struct redir *r);
int redir_sol_send(struct redir *r, unsigned char *buf, int blen);
int redir_sol_recv(struct redir *r);
int redir_data(struct redir *r);
