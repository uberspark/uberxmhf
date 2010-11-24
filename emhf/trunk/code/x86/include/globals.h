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

/**
 * globals.h - contains information about global variables used
 * throughout the hypervisor. Trying to keep them all in one place.
 */

#ifndef __GLOBALS_H__
#define __GLOBALS_H__

/**
 * XXX TODO At the moment the globals are organized by what C file
 * contains their actual (non-extern) definition.  This design
 * decision should be more carefully considered.  Ideally, there won't
 * be many globals, and they can all be collapsed into a single
 * structure.
 */ 

/**
 * Isolation Layer (islayer.c)
 */
typedef struct _islayer_globals {
    //the quiesce counter, all CPUs except for the one requesting the
    //quiesce will increment this when they get their quiesce signal
    u32 quiesce_counter;
    u32 lock_quiesce_counter; //spinlock to access the above
    
    //resume counter to rally all CPUs after resumption from quiesce
    u32 quiesce_resume_counter;
    u32 lock_quiesce_resume_counter; //spinlock to access the above
    
    //the quiesce variable and its lock
    u32 quiesce;      //if 1, then we have a quiesce in process
    u32 lock_quiesce; 
    
    //resume signal
    u32 quiesce_resume_signal; //signal becomes 1 to resume after quiescing
    u32 lock_quiesce_resume_signal; //spinlock to access the above
    
    // XXX not well-documented
    u32 ine820handler;
} ISLAYER_GLOBALS;

extern ISLAYER_GLOBALS g_islayer;

static inline void init_islayer_globals(ISLAYER_GLOBALS *g) {
    if(!g) return;
    
    g->quiesce_counter=0;
    g->lock_quiesce_counter=1;
    
    g->quiesce_resume_counter=0;
    g->lock_quiesce_resume_counter=1;
    
    g->quiesce=0;
    g->lock_quiesce=1; 
    
    g->quiesce_resume_signal=0;
    g->lock_quiesce_resume_signal=1;

    g->ine820handler=0;
}

/**
 * Runtime (runtime.c)
 */

typedef struct _runtime_globals {
    // XXX This MUST come first,
    // as g_runtime is used in place of midtable_numentries in runtimesup.S
    u32 midtable_numentries;

    u32 skinit_status_flag; // set to 1 after skinit has run on BSP
    
    u32 cpus_active; //number of CPUs that are awake, should be equal to
                       //midtable_numentries -1 if all went well with the
                       //MP startup protocol
    u32 lock_cpus_active; //spinlock to access the above
    
    u32 ap_go_signal; //go signal becomes 1 after BSP finishes rallying
    u32 lock_ap_go_signal; //spunlock to access the above
    
    u32 cleared_ucode; //number of CPUs whose ucode has been cleared
    u32 lock_cleared_ucode; // spinlock to access the above
    
} RUNTIME_GLOBALS;

extern RUNTIME_GLOBALS g_runtime;

static inline void init_runtime_globals(RUNTIME_GLOBALS *g) {
    if(!g) return;
    
    g->midtable_numentries = 0;

    // XXX When this defaults to 0 then we will attempt to skinit.
    // XXX Currently set to '1' to DISABLE skinit due to buggy HVM launch
    g->skinit_status_flag = 0; 
    
    g->cpus_active = 0;
    g->lock_cpus_active = 1;
    
    g->ap_go_signal = 0;
    g->lock_ap_go_signal = 1;
    
    g->cleared_ucode = 0;
    g->lock_cleared_ucode = 1;
}

#endif /* __GLOBALS_H__ */
