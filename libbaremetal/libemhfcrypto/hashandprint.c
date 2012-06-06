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

/* misc utility functions; probably belong elsewhere */
void hashandprint(const char* prefix __attribute__((unused)), const u8 *bytes, size_t len) {
    SHA_CTX ctx;
    u8 digest[SHA_DIGEST_LENGTH];
    //u64 start, end;

    printf("\nhashandprint: processing 0x%08x bytes at addr 0x%08x", len, (u32)bytes);
    
    //start = rdtsc64();
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    SHA1_Init(&ctx);
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    SHA1_Update(&ctx, bytes, len);
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    SHA1_Final(digest, &ctx);
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    //end = rdtsc64();
    //printf("\n%s (%u)", __FUNCTION__, __LINE__);
    //print_hex(prefix, digest, SHA_DIGEST_LENGTH);
    //printf("\n[PERF] hashandprint: elapsed CPU cycles 0x%016llx", end-start);    

    /* Simulate PCR 17 value on AMD processor */
    if(len == 0x10000) {
        u8 zeros[SHA_DIGEST_LENGTH];
        u8 pcr17[SHA_DIGEST_LENGTH];
        memset(zeros, 0, SHA_DIGEST_LENGTH);
        
        SHA1_Init(&ctx);
        SHA1_Update(&ctx, zeros, SHA_DIGEST_LENGTH);
        SHA1_Update(&ctx, digest, SHA_DIGEST_LENGTH);
        SHA1_Final(pcr17, &ctx);

        //print_hex("[AMD] Expected PCR-17: ", pcr17, SHA_DIGEST_LENGTH);
    }    
}
