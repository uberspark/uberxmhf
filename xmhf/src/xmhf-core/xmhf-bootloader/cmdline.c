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
 *  Remove unneeded command line arguments.
 *  Remove some parsing in parse_serial_param().
 *  Add boot_drive command line arguments.
 *  Rename get_option_val() to cmdline_get_option_val().
 *  Remove 3 functions when __DEBUG_SERIAL__ is not defined.
 *  Rename g_com_port to g_uart_config.
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

/*
 * copy of original command line
 * part of tboot measurement (hence in .text section)
 * FIXME - is this getting measured?
 */
char g_cmdline[CMDLINE_SIZE] = { 0 };

/*
 * the option names and default values must be separate from the actual
 * params entered
 * this allows the names and default values to be part of the MLE measurement
 * param_values[] need to be in .bss section so that will get cleared on launch
 */

/* global option array for command line */
static const cmdline_option_t g_tboot_cmdline_options[] = {
    { "loglvl",     "all" },         /* all|err,warn,info|none */
    { "logging",    "serial,vga" },  /* vga,serial,memory|none */
    { "serial",     "115200,8n1,0x3f8" },
    // XMHF: Add boot_drive command line arguments.
    { "boot_drive", "0x80" },
    /* serial=<baud>[/<clock_hz>][,<DPS>[,<io-base>[,<irq>[,<serial-bdf>[,<bridge-bdf>]]]]] */
    // XMHF: Remove unneeded command line arguments.
    //{ "vga_delay",  "0" },           /* # secs */
    //{ "ap_wake_mwait", "false" },    /* true|false */
    //{ "pcr_map", "legacy" },         /* legacy|da */
    //{ "min_ram", "0" },              /* size in bytes | 0 for no min */
    //{ "call_racm", "false" },        /* true|false|check */
    //{ "measure_nv", "false" },       /* true|false */
    //{ "extpol",    "sha256" },         /*agile|embedded|sha1|sha256|sm3|... */
    //{ "ignore_prev_err", "true"},    /* true|false */
    //{ "force_tpm2_legacy_log", "false"}, /* true|false */
    //{ "save_vtd", "false"},          /* true|false */
    //{ "dump_memmap", "false"},          /* true|false */
    { NULL, NULL }
};
static char g_tboot_param_values[ARRAY_SIZE(g_tboot_cmdline_options)][MAX_VALUE_LEN];

void tboot_parse_cmdline(void)
{
    cmdline_parse(g_cmdline, g_tboot_cmdline_options, g_tboot_param_values);
}

// XMHF: Remove 3 functions when __DEBUG_SERIAL__ is not defined.
#ifdef __DEBUG_SERIAL__

static bool parse_com_fmt(const char **fmt)
{
    /* fmt:  <5|6|7|8><n|o|e|m|s><0|1> */
    /* default 8n1 */
    uint8_t data_bits = 8;
    uint8_t parity = 'n';
    uint8_t stop_bits = 1;


    /* must specify all values */
    if ( strlen(*fmt) < 3 )
        return false;

    /* data bits */
    if ( **fmt >= '5' && **fmt <= '8' )
        data_bits = **fmt - '0';
    else
        return false;
    (*fmt)++;

    /* parity */
    if ( **fmt == 'n' || **fmt == 'o' || **fmt == 'e' || **fmt == 'm' ||
         **fmt == 's' )
        parity = **fmt;
    else
        return false;
    (*fmt)++;

    /* stop bits */
    if ( **fmt == '0' || **fmt == '1' )
        stop_bits = **fmt - '0';
    else
        return false;
    (*fmt)++;

    g_uart_config.comc_fmt = GET_LCR_VALUE(data_bits, stop_bits, parity);

    return true;
}

static bool parse_serial_param(const char *com)
{
    /* parse baud */
    g_uart_config.comc_curspeed = strtoul(com, &com, 10);
    if ( (g_uart_config.comc_curspeed < 1200) ||
         (g_uart_config.comc_curspeed > 115200) )
        return false;

    /* parse clock hz */
    if ( *com == '/' ) {
        ++com;
        g_uart_config.comc_clockhz = strtoul(com, &com, 0) << 4;
        if ( g_uart_config.comc_clockhz == 0 )
            return false;
    }

    /* parse data_bits/parity/stop_bits */
    if ( *com != ',' )
        goto exit;
    ++com;
    while ( isspace(*com) )
        com++;
    if ( !parse_com_fmt(&com) )
        return false;

    /* parse IO base */
    if ( *com != ',' )
        goto exit;
    ++com;
    g_uart_config.comc_port = strtoul(com, &com, 0);
    if ( g_uart_config.comc_port == 0 )
        return false;

    // XMHF: Remove some parsing in parse_serial_param().
    ///* parse irq */
    //if ( *com != ',' )
    //    goto exit;
    //++com;
    //g_uart_config.comc_irq = strtoul(com, (char **)&com, 10);
    //if ( g_uart_config.comc_irq == 0 )
    //    return false;
    //
    ///* parse PCI serial controller bdf */
    //if ( *com != ',' )
    //    goto exit;
    //++com;
    //if ( !parse_com_psbdf(&com) )
    //    return false;
    //
    ///* parse PCI bridge bdf */
    //if ( *com != ',' )
    //    goto exit;
    //++com;
    //if ( !parse_com_pbbdf(&com) )
    //    return false;

 exit:
    return true;
}

bool get_tboot_serial(void)
{
    // XMHF: Rename get_option_val() to cmdline_get_option_val().
    const char *serial = cmdline_get_option_val(g_tboot_cmdline_options,
                                        g_tboot_param_values, "serial");
    if ( serial == NULL || *serial == '\0' )
        return false;

    return parse_serial_param(serial);
}

// XMHF: Remove 3 functions when __DEBUG_SERIAL__ is not defined.
#endif /* __DEBUG_SERIAL__ */

// XMHF: Add boot_drive command line arguments.
u8 get_tboot_boot_drive(void)
{
    const char *boot_drive = cmdline_get_option_val(g_tboot_cmdline_options,
                                                    g_tboot_param_values,
                                                    "boot_drive");
    if (boot_drive == NULL) {
        return 0x80u;
    }
    return (u8)strtoul(boot_drive, NULL, 0);
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
