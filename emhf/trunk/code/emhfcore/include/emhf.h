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
#ifndef __ASSEMBLY__
	#include <stdint.h>
	#include <stdbool.h>
	#include <stddef.h>
	#include <string.h>
#endif /* __ASSEMBLY__ */

//XXX: arch. specific headers, need to move into include/arch folder
#include <_ctype.h>		//the ctype variable definition for debug printf
#include <_com.h>		//serial UART as debugging backend
#include <_multiboot.h>  //boot manager (multiboot)
#include <_cmdline.h>	//GRUB command line handling functions
#include <_error.h>      //error handling and assertions
#include <_processor.h>  //CPU
#include <_msr.h>        //model specific registers
#include <_paging.h>     //MMU
#include <_io.h>         //legacy I/O
#include <_apic.h>       //APIC
#include <_svm.h>        //SVM extensions
#include <_vmx.h>				//VMX extensions
#include <_txt.h>		//Trusted eXecution Technology (SENTER support)
#include <_pci.h>        //PCI bus glue
#include <_acpi.h>				//ACPI glue
#include <_svm_eap.h>		//SVM DMA protection
#include <_vmx_eap.h>		//VMX DMA protection
#include <_tpm.h>			//generic TPM functions
#include <_tpm_emhf.h>		//EMHF-specific TPM functions
#include <_sarg.h>			//language specifics
#include <_div64.h>			//do_div for debug output
#include <_perf.h>			//performance measurement routines


#include <emhf-types.h>		//EMHF specific base types
#include <_globals.h>		//XXX: need to get rid of this

//----------------------------------------------------------------------
// component headers
#include <emhf-sl.h>		//EMHF secure loader component
#include <emhf-runtime.h>		//EMHF secure loader component
#include <emhf-debug.h>		//EMHF debug component
#include <emhf-memprot.h>	//EMHF memory protection component
#include <emhf-dmaprot.h>	//EMHF DMA protection component
#include <emhf-parteventhub.h>	//EMHF partition event-hub component
#include <emhf-smpguest.h>		//EMHF SMP guest component
#include <emhf-xcphandler.h>	//EMHF exception handler component
#include <emhf-baseplatform.h>	//EMHF base platform component


#endif /* __EMHF_H_ */
