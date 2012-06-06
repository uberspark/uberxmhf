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

//emhf.h - main EMHF core header file 
// this orchestrates the inclusion of other core component specific
// headers
//author: amit vasudevan (amitvasudevan@acm.org)
//
#ifndef __EMHF_H_
#define __EMHF_H_


//pull in required C99 compatible C-library interfaces
//libemhfc
#ifndef __ASSEMBLY__
	#include <stdint.h>
	#include <stdbool.h>
	#include <stddef.h>
	#include <stdarg.h>
	#include <stdio.h>
	#include <string.h>
	#include <ctype.h>
	#include <assert.h>
#endif /* __ASSEMBLY__ */

//pull in required crypto (SHA-1)
//libemhfcrypto
#ifndef __ASSEMBLY__
	#include <tomcrypt.h>
	#include <sha1.h>
#endif /* __ASSEMBLY__ */


//pull in required TPM library
//libtpm
#ifndef __ASSEMBLY__
	#include <tpm.h>
#endif /* __ASSEMBLY__ */

#include <emhf-debug.h>			//EMHF debug component 
#include <emhf-types.h>			//EMHF specific base types



//forward declaration of runtime parameter block
#ifndef __ASSEMBLY__
extern RPB *rpb;	
#endif	//__ASSEMBLY__


//----------------------------------------------------------------------
// component headers
#include <emhf-baseplatform.h>	//EMHF base platform component
#include <emhf-memprot.h>		//EMHF memory protection component
#include <emhf-dmaprot.h>		//EMHF DMA protection component
#include <emhf-partition.h>		//EMHF partition component
#include <emhf-smpguest.h>		//EMHF SMP guest component
#include <emhf-parteventhub.h>	//EMHF partition event-hub component
#include <emhf-xcphandler.h>	//EMHF exception handler component
#include <emhf-tpm.h>			//EMHF Trusted Platform Module component
#include <emhf-sl.h>			//EMHF secure loader component
#include <emhf-runtime.h>		//EMHF secure loader component
#include <emhf-app.h>			//EMHF Application callback declarations


#endif /* __EMHF_H_ */
