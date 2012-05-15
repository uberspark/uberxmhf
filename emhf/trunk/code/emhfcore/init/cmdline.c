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

/*
 * cmdline.c: command line parsing fns
 *
 * Copyright (c) 2006-2010, Intel Corporation
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

/**
 * Modified for EMHF.
 */

#include <emhf.h> 

#define ARRAY_SIZE(a)     (sizeof(a) / sizeof((a)[0]))

/*
 * copy of original command line
 * part of tboot measurement (hence in .text section)
 * FIXME - is this getting measured?
 */
char g_cmdline[CMDLINE_SIZE] = { 0 };

/* Used for kernel command line parameter setup */
typedef struct {
    const char *name;          /* set to NULL for last item in list */
    const char *def_val;
} cmdline_option_t;

#define MAX_VALUE_LEN 64

/*
 * the option names and default values must be separate from the actual
 * params entered
 * this allows the names and default values to be part of the MLE measurement
 * param_values[] need to be in .bss section so that will get cleared on launch
 */

/* global option array for command line */
static const cmdline_option_t g_tboot_cmdline_options[] = {
    { "loglvl",     "all" },     /* all|none */
    { "logging",    "serial,vga" },  /* vga,serial,memory|none */
    { "serial",     "115200,8n1,0x3f8" },
    /* serial=<baud>[/<clock_hz>][,<DPS>[,<io-base>[,<irq>[,<serial-bdf>[,<bridge-bdf>]]]]] */

    /* { "vga_delay",  "0" },      /\* # secs *\/ */
    /* { "no_usb",     "true" },   /\* true|false *\/ */
    { "nvpalpcr0", "0000000000000000000000000000000000000000"}, /* Req'd PCR[0] of NvMuxPal */
    { "nvenforce", "true" }, /* true|false - actually enforce nvpalpcr0? */
    { NULL, NULL }
};

static const cmdline_option_t g_linux_cmdline_options[] = {
    { "vga", "" },
    { "mem", "" },
    { NULL, NULL }
};
/* static char g_linux_param_values[ARRAY_SIZE(g_linux_cmdline_options)][MAX_VALUE_LEN]; */
static char g_tboot_param_values[ARRAY_SIZE(g_tboot_cmdline_options)][MAX_VALUE_LEN];

static const char* get_option_val(const cmdline_option_t *options,
                                  char vals[][MAX_VALUE_LEN],
                                  const char *opt_name)
{
    int i;
    for ( i = 0; options[i].name != NULL; i++ ) {
        if ( strcmp(options[i].name, opt_name) == 0 )
            return vals[i];
    }
    printf("requested unknown option: %s\n", opt_name);
    return NULL;
}

static void cmdline_parse(char *cmdline, const cmdline_option_t *options,
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
        /* skip whitespace */
        while ( isspace(*p) )
            p++;
        if ( *p == '\0' )
            break;

        {
            /* find end of current option */
            const char *opt_start = p;
            const char *opt_end = strchr(opt_start, ' ');
            if ( opt_end == NULL )
                opt_end = opt_start + strlen(opt_start);
            p = opt_end;

            {
                /* find value part; if no value found, use default and continue */
                const char *val_start = strchr(opt_start, '=');
                if ( val_start == NULL || val_start > opt_end )
                    continue;
                val_start++;

                {
                    unsigned int opt_name_size = val_start - opt_start - 1;
                    unsigned int copy_size = opt_end - val_start;
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
        }
    }
}

bool cmdline_get_nvenforce(void) {
    const char *nvenforce = get_option_val(g_tboot_cmdline_options,
                                           g_tboot_param_values, "nvenforce");
    if ( nvenforce == NULL || *nvenforce == '\0' )
        return true; /* desired default behavior is YES, DO ENFORCE */

    if ( strncmp(nvenforce, "false", 6 ) == 0 )
        return false;

    return true;
}

/* lazy translation table to go from ascii hex to binary, one nibble
 * at a time */
const uint8_t asc2nib[] = {
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0,
    0, 0, 0, 0, 0, 10, 11, 12, 13, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 11, 12,
    13, 14, 15 }; /* don't bother going past 'f' */
#define ASC2NIB(x) ((x) < 103 ? asc2nib[x] : 0)

/* allow caller to query whether param exists on cmdline by invoking
 * with NULL */
bool cmdline_get_nvpalpcr0(uint8_t *reqd_pcr0) {
    int i;
    const char *ascii = get_option_val(g_tboot_cmdline_options,
                                       g_tboot_param_values, "nvpalpcr0");
    if ( ascii == NULL || *ascii == '\0' )
        return false; /* no param found */

    if ( reqd_pcr0 == NULL )
        return true;

    for(i=0; i<20; i++)
        reqd_pcr0[i] = (ASC2NIB((uint8_t)ascii[2*i]) << 4) | ASC2NIB((uint8_t)ascii[2*i+1]);

    return true;
}

void tboot_parse_cmdline(void)
{
    cmdline_parse(g_cmdline, g_tboot_cmdline_options, g_tboot_param_values);
}

/* void linux_parse_cmdline(char *cmdline) */
/* { */
/*     cmdline_parse(cmdline, g_linux_cmdline_options, g_linux_param_values); */
/* } */

void get_tboot_loglvl(void)
{
    const char *loglvl = get_option_val(g_tboot_cmdline_options,
                                        g_tboot_param_values, "loglvl");
    if ( loglvl == NULL )
        return;

    if ( strcmp(loglvl, "none") == 0 )
        g_log_level = LOG_LEVEL_NONE; /* print nothing */
}

void get_tboot_log_targets(void)
{
    const char *targets = get_option_val(g_tboot_cmdline_options,
                                         g_tboot_param_values, "logging");

    /* nothing set, leave defaults */
    if ( targets == NULL || *targets == '\0' )
        return;

    /* determine if no targets set explicitly */
    if ( strcmp(targets, "none") == 0 ) {
        g_log_targets = LOG_TARGET_NONE; /* print nothing */
        return;
    }

    /* else init to nothing and parse the possible targets */
    g_log_targets = LOG_TARGET_NONE;

    while ( *targets != '\0' ) {
        if ( strncmp(targets, "memory", 6) == 0 ) {
            g_log_targets |= LOG_TARGET_MEMORY;
            targets += 6;
        }
        else if ( strncmp(targets, "serial", 6) == 0 ) {
            g_log_targets |= LOG_TARGET_SERIAL;
            targets += 6;
        }
        else if ( strncmp(targets, "vga", 3) == 0 ) {
            g_log_targets |= LOG_TARGET_VGA;
            targets += 3;
        }
        else 
            break; /* unrecognized, end loop */

        if ( *targets == ',' )
            targets++;
        else
            break; /* unrecognized, end loop */
    }
}

/* static bool parse_pci_bdf(const char **bdf, uint32_t *bus, uint32_t *slot, */
/*                           uint32_t *func) */
/* { */
/*     *bus = strtoul(*bdf, bdf, 16); */
/*     if ( **bdf != ':' ) */
/*         return false; */
/*     (*bdf)++; */
/*     *slot = strtoul(*bdf, bdf, 16); */
/*     if ( **bdf != '.' ) */
/*         return false; */
/*     (*bdf)++; */
/*     *func = strtoul(*bdf, bdf, 16); */

/*     return true; */
/* } */

/* bool g_psbdf_enabled = false; */
/* static bool parse_com_psbdf(const char **bdf) */
/* { */
/*     g_psbdf_enabled = parse_pci_bdf(bdf, */
/*                   &g_com_port.comc_psbdf.bus, */
/*                   &g_com_port.comc_psbdf.slot, */
/*                   &g_com_port.comc_psbdf.func); */

/*     return g_psbdf_enabled; */
/* } */

/* bool g_pbbdf_enabled = false; */
/* static bool parse_com_pbbdf(const char **bdf) */
/* { */
/*     g_pbbdf_enabled = parse_pci_bdf(bdf, */
/*                   &g_com_port.comc_pbbdf.bus, */
/*                   &g_com_port.comc_pbbdf.slot, */
/*                   &g_com_port.comc_pbbdf.func); */

/*     return g_pbbdf_enabled; */
/* } */

static bool parse_com_fmt(const char **fmt)
{
    /* fmt:  <5|6|7|8><n|o|e|m|s><0|1> */
    /* default 8n1 */
    /* uint8_t data_bits = 8; */
    /* uint8_t parity = 'n'; */
    /* uint8_t stop_bits = 1; */

    /* must specify all values */
    if ( strlen(*fmt) < 3 )
        return false;

    /* data bits */
    if ( **fmt >= '5' && **fmt <= '8' )
        g_uart_config.data_bits = **fmt - '0';
    else
        return false;
    (*fmt)++;

    /* parity */
    if ( **fmt == 'n' || **fmt == 'o' || **fmt == 'e' || **fmt == 'm' ||
         **fmt == 's' )
        g_uart_config.parity = 
            (**fmt == 'n')
            ? PARITY_NONE
            : (**fmt == 'o')
            ? PARITY_ODD
            : (**fmt == 'e')
            ? PARITY_EVEN
            : (**fmt == 'm')
            ? PARITY_MARK
            : PARITY_SPACE;
    else
        return false;
    (*fmt)++;

    /* stop bits */
    if ( **fmt == '0' || **fmt == '1' )
        g_uart_config.stop_bits = **fmt - '0';
    else
        return false;
    (*fmt)++;

    return true;
}

static bool parse_serial_param(const char *com)
{
    /* parse baud */
    g_uart_config.baud = strtoul(com, &com, 10);
    if ( (g_uart_config.baud < 1200) ||
         (g_uart_config.baud > 115200) )
        return false;

    /* parse clock hz */
    if ( *com == '/' ) {
        ++com;
        g_uart_config.clock_hz = strtoul(com, &com, 0) << 4;
        if ( g_uart_config.clock_hz == 0 )
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
    g_uart_config.port = strtoul(com, &com, 0);
    if ( g_uart_config.port == 0 )
        return false;

    /* we don't handle additional params */
    if ( *com == ',' ) {
        return false;
    }

    /* parse irq */
    /* if ( *com != ',' ) */
    /*     goto exit; */
    /* ++com; */
    /* g_com_port.comc_irq = strtoul(com, &com, 10); */
    /* if ( g_com_port.comc_irq == 0 ) */
    /*     return false; */

    /* /\* parse PCI serial controller bdf *\/ */
    /* if ( *com != ',' ) */
    /*     goto exit; */
    /* ++com; */
    /* if ( !parse_com_psbdf(&com) ) */
    /*     return false; */

    /* /\* parse PCI bridge bdf *\/ */
    /* if ( *com != ',' ) */
    /*     goto exit; */
    /* ++com; */
    /* if ( !parse_com_pbbdf(&com) ) */
    /*     return false; */

 exit:
    return true;
}

bool get_tboot_serial(void)
{
    const char *serial = get_option_val(g_tboot_cmdline_options,
                                        g_tboot_param_values, "serial");
    if ( serial == NULL || *serial == '\0' )
        return false;

    return parse_serial_param(serial);
}

/* void get_tboot_vga_delay(void) */
/* { */
/*     const char *vga_delay = get_option_val(g_tboot_cmdline_options, */
/*                                            g_tboot_param_values, "vga_delay"); */
/*     if ( vga_delay == NULL ) */
/*         return; */

/*     g_vga_delay = strtoul(vga_delay, NULL, 0); */
/* } */

/* void get_tboot_no_usb(void) */
/* { */
/*     const char *no_usb = get_option_val(g_tboot_cmdline_options, */
/*                                         g_tboot_param_values, "no_usb"); */
/*     if ( no_usb == NULL ) */
/*         return; */

/*     g_no_usb = ( strcmp(no_usb, "true") == 0 ); */
/* } */


/*
 * linux kernel command line parsing
 */

/* bool get_linux_vga(int *vid_mode) */
/* { */
/*     const char *vga = get_option_val(g_linux_cmdline_options, */
/*                                      g_linux_param_values, "vga"); */
/*     if ( vga == NULL || vid_mode == NULL ) */
/*         return false; */

/*     if ( strcmp(vga, "normal") == 0 ) */
/*         *vid_mode = 0xFFFF; */
/*     else if ( strcmp(vga, "ext") == 0 ) */
/*         *vid_mode = 0xFFFE; */
/*     else if ( strcmp(vga, "ask") == 0 ) */
/*         *vid_mode = 0xFFFD; */
/*     else */
/*         *vid_mode = strtoul(vga, NULL, 0); */

/*     return true; */
/* } */

/* bool get_linux_mem(uint64_t *max_mem) */
/* { */
/*     char *last = NULL; */
/*     const char *mem = get_option_val(g_linux_cmdline_options, */
/*                                      g_linux_param_values, "mem"); */
/*     if ( mem == NULL || max_mem == NULL ) */
/*         return false; */

/*     *max_mem = strtoul(mem, &last, 0); */
/*     if ( *max_mem == 0 ) */
/*         return false; */

/*     if ( last == NULL ) */
/*         return true; */

/*     switch ( *last ) { */
/*         case 'G': */
/*         case 'g': */
/*             *max_mem = *max_mem << 30; */
/*             return true; */
/*         case 'M': */
/*         case 'm': */
/*             *max_mem = *max_mem << 20; */
/*             return true; */
/*         case 'K': */
/*         case 'k': */
/*             *max_mem = *max_mem << 10; */
/*             return true; */
/*         default: */
/*             return false; */
/*     } */

/*     return true; */
/* } */

/* const char *skip_filename(const char *cmdline) */
/* { */
/*     if ( cmdline == NULL || *cmdline == '\0' ) */
/*         return cmdline; */

/*     /\* strip leading spaces, file name, then any spaces until the next */
/*      non-space char (e.g. "  /foo/bar   baz" -> "baz"; "/foo/bar" -> "")*\/ */
/*     while ( *cmdline != '\0' && isspace(*cmdline) ) */
/*         cmdline++; */
/*     while ( *cmdline != '\0' && !isspace(*cmdline) ) */
/*         cmdline++; */
/*     while ( *cmdline != '\0' && isspace(*cmdline) ) */
/*         cmdline++; */
/*     return cmdline; */
/* } */


/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
