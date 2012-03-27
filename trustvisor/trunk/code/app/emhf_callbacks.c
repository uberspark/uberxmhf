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

#include <emhf.h>

u32 tv_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb);
u32 tv_app_handlehypercall(VCPU *vcpu, struct regs *r);
u32 tv_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
                                            struct regs *r, u64 gpa, u64 gva, u64 violationcode);
u32 tv_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, 
                                      u32 portnum, u32 access_type, u32 access_size);
void tv_app_handleshutdown(VCPU *vcpu, struct regs *r);

u32 emhf_app_main(VCPU *vcpu, APP_PARAM_BLOCK *apb)
{
  return tv_app_main(vcpu, apb);
}

u32 emhf_app_handlehypercall(VCPU *vcpu, struct regs *r)
{
  return tv_app_handlehypercall(vcpu, r);
}

u32 emhf_app_handleintercept_hwpgtblviolation(VCPU *vcpu,
                                              struct regs *r, u64 gpa, u64 gva, u64 violationcode)
{
  return tv_app_handleintercept_hwpgtblviolation(vcpu, r, gpa, gva, violationcode);
}

u32 emhf_app_handleintercept_portaccess(VCPU *vcpu, struct regs *r, 
                                        u32 portnum, u32 access_type, u32 access_size)
{
  return tv_app_handleintercept_portaccess(vcpu, r, portnum, access_type, access_size);
}

void emhf_app_handleshutdown(VCPU *vcpu, struct regs *r)
{
  tv_app_handleshutdown(vcpu, r);
}
