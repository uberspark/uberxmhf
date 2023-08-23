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

/*
 * XMHF: The following file is taken from:
 *  tboot-1.10.5/tboot/common/cmdline.c
 * Changes made include:
 *  Split to xmhf-bootloader/cmdline.c and xmhf-bootloader/cmdline.c .
 *  Rename get_option_val() to cmdline_get_option_val(), make it non-static.
 *  Make cmdline_parse() non-static.
 * The list of symbols in the order of appearance in cmdline.c is:
 *  symbol                          location
 *  g_cmdline                       xmhf-bootloader/cmdline.c
 *  cmdline_option_t                libxmhfutil/include/cmdline.h
 *  MAX_VALUE_LEN                   libxmhfutil/include/cmdline.h
 *  g_tboot_cmdline_options         xmhf-bootloader/cmdline.c
 *  g_tboot_param_values            xmhf-bootloader/cmdline.c
 *  g_linux_cmdline_options         discarded
 *  g_linux_param_values            discarded
 *  tb_loglvl_map_t                 discarded
 *  g_loglvl_map                    discarded
 *  get_option_val                  libxmhfutil/cmdline.c
 *  cmdline_parse                   libxmhfutil/cmdline.c
 *  tboot_parse_cmdline             xmhf-bootloader/cmdline.c
 *  linux_parse_cmdline             discarded
 *  get_loglvl_prefix               discarded
 *  get_tboot_loglvl                discarded
 *  get_tboot_log_targets           discarded
 *  parse_pci_bdf                   discarded
 *  g_psbdf_enabled                 discarded
 *  parse_com_psbdf                 discarded
 *  g_pbbdf_enabled                 discarded
 *  parse_com_pbbdf                 discarded
 *  parse_com_fmt                   xmhf-bootloader/cmdline.c
 *  parse_serial_param              xmhf-bootloader/cmdline.c
 *  get_tboot_serial                xmhf-bootloader/cmdline.c
 *  get_tboot_vga_delay             discarded
 *  get_tboot_prefer_da             discarded
 *  g_min_ram                       discarded
 *  get_tboot_min_ram               discarded
 *  get_tboot_mwait                 discarded
 *  get_tboot_call_racm             discarded
 *  get_tboot_call_racm_check       discarded
 *  get_tboot_measure_nv            discarded
 *  get_tboot_extpol                discarded
 *  get_tboot_force_tpm2_legacy_log discarded
 *  get_tboot_ignore_prev_err       discarded
 *  get_tboot_save_vtd              discarded
 *  get_tboot_dump_memmap           discarded
 *  get_linux_vga                   discarded
 *  get_linux_mem                   discarded
 */

/*
 * cmdline.c: command line parsing fns
 *
 * Copyright (c) 2006-2012, Intel Corporation
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *   * Redistributions of source code must retain the above copyright
 *     notice, this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above
 *     copyright notice, this list of conditions and the following
 *     disclaimer in the documentation and/or other materials provided
 *     with the distribution.
 *   * Neither the name of the Intel Corporation nor the names of its
 *     contributors may be used to endorse or promote products derived
 *     from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#include <xmhf.h>
#include <cmdline.h>

const char* cmdline_get_option_val(const cmdline_option_t *options,  char vals[][MAX_VALUE_LEN],    const char *opt_name)
{
    for ( int i = 0; options[i].name != NULL; i++ ) {
        if ( strcmp(options[i].name, opt_name) == 0 )
            return vals[i];
    }
    printf("requested unknown option: %s\n", opt_name);
    return NULL;
}

void cmdline_parse(const char *cmdline, const cmdline_option_t *options,
                          char vals[][MAX_VALUE_LEN])
{
    const char *p = cmdline;
    int i;

    /* copy default values to vals[] */
    for ( i = 0; options[i].name != NULL; i++ ) {
        strncpy(vals[i], options[i].def_val, MAX_VALUE_LEN-1);
        vals[i][MAX_VALUE_LEN-1] = '\0';
    }

    if ( p == NULL )
        return;

    /* parse options */
    while ( true )
    {
        const char *opt_start;
        const char *opt_end;
        const char *val_start;
        unsigned int opt_name_size;
        unsigned int copy_size;

        /* skip whitespace */
        while ( isspace(*p) )
            p++;
        if ( *p == '\0' )
            break;

        /* find end of current option */
        opt_start = p;
        opt_end = strchr(opt_start, ' ');
        if ( opt_end == NULL )
            opt_end = opt_start + strlen(opt_start);
        p = opt_end;

        /* find value part; if no value found, use default and continue */
        val_start = strchr(opt_start, '=');
        if ( val_start == NULL || val_start > opt_end )
            continue;
        val_start++;

        opt_name_size = val_start - opt_start - 1;
        copy_size = opt_end - val_start;
        if ( copy_size > MAX_VALUE_LEN - 1 )
            copy_size = MAX_VALUE_LEN - 1;
        if ( opt_name_size == 0 || copy_size == 0 )
            continue;

        /* value found, so copy it */
        for ( i = 0; options[i].name != NULL; i++ ) {
            if ( strncmp(options[i].name, opt_start, opt_name_size ) == 0 ) {
                strncpy(vals[i], val_start, copy_size);
                vals[i][copy_size] = '\0'; /* add '\0' to the end of string */
                break;
            }
        }
    }
}

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
