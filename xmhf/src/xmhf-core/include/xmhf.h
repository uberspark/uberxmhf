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

//xmhf.h - main EMHF core header file 
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

#include <xmhf-debug.h>			//EMHF debug component 
#include <xmhf-types.h>			//EMHF specific base types



//forward declaration of runtime parameter block
#ifndef __ASSEMBLY__
extern RPB *rpb;	
#endif	//__ASSEMBLY__


//----------------------------------------------------------------------
// component headers
#include <xmhf-baseplatform.h>	//EMHF base platform component
#include <xmhf-memprot.h>		//EMHF memory protection component
#include <xmhf-dmaprot.h>		//EMHF DMA protection component
#include <xmhf-partition.h>		//EMHF partition component
#include <xmhf-smpguest.h>		//EMHF SMP guest component
#include <xmhf-parteventhub.h>	//EMHF partition event-hub component
#include <xmhf-xcphandler.h>	//EMHF exception handler component
#include <xmhf-tpm.h>			//EMHF Trusted Platform Module component
#include <xmhf-sl.h>			//EMHF secure loader component
#include <xmhf-runtime.h>		//EMHF secure loader component
#include <xmhf-app.h>			//EMHF Application callback declarations


#endif /* __EMHF_H_ */
