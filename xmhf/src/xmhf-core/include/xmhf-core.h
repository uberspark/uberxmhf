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

//xmhf.h - main XMHF core header file 
// this orchestrates the inclusion of other core component specific
// headers
//author: amit vasudevan (amitvasudevan@acm.org)
//
#ifndef __XMHF_CORE_H_
#define __XMHF_CORE_H_

#include <xmhf.h>


//pull in required crypto (SHA-1)
//libXMHFcrypto
#ifndef __ASSEMBLY__
	#include <xmhfcrypto.h>
	#include <sha1.h>
#endif /* __ASSEMBLY__ */


//pull in required TPM library
//libtpm
#ifndef __ASSEMBLY__
	#include <tpm.h>
#endif /* __ASSEMBLY__ */

/*//forward declaration of runtime parameter block
#ifndef __ASSEMBLY__
extern RPB *rpb;	
#endif	//__ASSEMBLY__
*/

//----------------------------------------------------------------------
// component headers
#include <xc-baseplatform.h>	//base platform component
#include <xc-memprot.h>			//memory protection component
#include <xc-dmaprot.h>			//DMA protection component
#include <xc-partition.h>		//partition component
#include <xc-richguest.h>		//rich guest component
#include <xc-parteventhub.h>	//partition event-hub component
#include <xc-xcphandler.h>		//exception handler component
#include <xc-tpm.h>				//Trusted Platform Module component
#include <xc-startup.h>			//secure loader component
#include <xc-hypapp.h>			//hypapp callback declarations
#include <xc-apihub.h>			//core API interface component


#endif /* __XMHF_CORE_H_ */
