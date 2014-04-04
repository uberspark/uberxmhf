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

// xmhf.h - main XMHF header file 
// author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __XMHF_H_
#define __XMHF_H_

#ifndef __ASSEMBLY__

//pull in required libxmhfc C includes
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>

//	#ifndef __XMHF_VERIFICATION__
//		#include <assert.h>
//	#endif
#endif // __ASSEMBLY__ 

//pull in required crypto (SHA-1)
//libXMHFcrypto
//#ifndef __ASSEMBLY__
//	#include <xmhfcrypto.h>
//	#include <sha1.h>
//#endif // __ASSEMBLY__


//pull in required TPM library
//libtpm
//#ifndef __ASSEMBLY__
//	#include <tpm.h>
//#endif // __ASSEMBLY__ 

#include <xmhf-types.h>			//XMHF specific base types
#include <xmhf-debug.h>			//libxmhfdebug
#include <xmhf-error.h> 

#ifdef __XMHF_VERIFICATION__
	//include verification related primitives
	#include <xmhf-verification.h>
#endif //__XMHF_VERIFICATION__

/*
//forward declaration of runtime parameter block
#ifndef __ASSEMBLY__
extern RPB *rpb;	
#endif	//__ASSEMBLY__


//----------------------------------------------------------------------
// component headers
#include <xmhf-baseplatform.h>	//XMHF base platform component
#include <xmhf-memprot.h>		//XMHF memory protection component
#include <xmhf-dmaprot.h>		//XMHF DMA protection component
#include <xmhf-partition.h>		//XMHF partition component
#include <xmhf-smpguest.h>		//XMHF SMP guest component
#include <xmhf-parteventhub.h>	//XMHF partition event-hub component
#include <xmhf-xcphandler.h>	//XMHF exception handler component
#include <xmhf-tpm.h>			//XMHF Trusted Platform Module component
#include <xmhf-sl.h>			//XMHF secure loader component
#include <xmhf-runtime.h>		//XMHF secure loader component
#include <xmhf-app.h>			//XMHF Application callback declarations
#include <xmhf-apihub.h>		//XMHF core API interface component
*/

#endif /* __XMHF_H_ */
