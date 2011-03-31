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

#include "CException.h"

volatile CEXCEPTION_FRAME_T CExceptionFrames[CEXCEPTION_NUM_ID];

//------------------------------------------------------------------------------------------
//  Throw
//------------------------------------------------------------------------------------------
void Throw(CEXCEPTION_T ExceptionID)
{
    unsigned int MY_ID = CEXCEPTION_GET_ID;
    CExceptionFrames[MY_ID].Exception = ExceptionID;
    longjmp(*CExceptionFrames[MY_ID].pFrame, 1);
}

//------------------------------------------------------------------------------------------
//  Explaination of what it's all for:
//------------------------------------------------------------------------------------------
/*
#define Try                                                         
    {                                                                   <- give us some local scope.  most compilers are happy with this
        jmp_buf *PrevFrame, NewFrame;                                   <- prev frame points to the last try block's frame.  new frame gets created on stack for this Try block
        unsigned int MY_ID = CEXCEPTION_GET_ID;                         <- look up this task's id for use in frame array.  always 0 if single-tasking
        PrevFrame = CExceptionFrames[CEXCEPTION_GET_ID].pFrame;         <- set pointer to point at old frame (which array is currently pointing at)
        CExceptionFrames[MY_ID].pFrame = &NewFrame;                     <- set array to point at my new frame instead, now
        CExceptionFrames[MY_ID].Exception = CEXCEPTION_NONE;            <- initialize my exception id to be NONE
        if (setjmp(NewFrame) == 0) {                                    <- do setjmp.  it returns 1 if longjump called, otherwise 0
            if (&PrevFrame)                                             <- this is here to force proper scoping.  it requires braces or a single line to be but after Try, otherwise won't compile.  This is always true at this point.

#define Catch(e)                                                    
            else { }                                                    <- this also forces proper scoping.  Without this they could stick their own 'else' in and it would get ugly
            CExceptionFrames[MY_ID].Exception = CEXCEPTION_NONE;        <- no errors happened, so just set the exception id to NONE (in case it was corrupted)
        }                                                           
        else                                                            <- an exception occurred
        { e = CExceptionFrames[MY_ID].Exception; e=e;}                  <- assign the caught exception id to the variable passed in.  
        CExceptionFrames[MY_ID].pFrame = PrevFrame;                     <- make the pointer in the array point at the previous frame again, as if NewFrame never existed.
    }                                                                   <- finish off that local scope we created to have our own variables
    if (CExceptionFrames[CEXCEPTION_GET_ID].Exception != CEXCEPTION_NONE)  <- start the actual 'catch' processing if we have an exception id saved away
 */

