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
 * Modified for XMHF by Amit Vasudevan (amitvasudevan@acm.org)
 */

#include <xmhf.h>
#include <xmhf-hwm.h>
#include <xmhfhw.h>
#include <xmhf-debug.h>

#include "cmdline.h"


#ifndef ULONG_MAX
#define ULONG_MAX     0xFFFFFFFFUL
#endif

/*
 * Convert a string to an unsigned long integer.
 *
 * Ignores `locale' stuff.  Assumes that the upper and lower case
 * alphabets and digits are each contiguous.
 */
static unsigned long cmdline_strtoul(const char *nptr, const char **endptr, unsigned int base)
{
	const char *s = nptr;
	unsigned long acc;
	unsigned char c;
	unsigned long cutoff;
	int neg = 0, any, cutlim;

	/*
	 * See strtol for comments as to the logic used.
	 */
	do {
		c = *s++;
	} while (isspace(c));
	if (c == '-') {
		neg = 1;
		c = *s++;
	} else if (c == '+')
		c = *s++;
	if ((base == 0 || base == 16) &&
	    c == '0' && (*s == 'x' || *s == 'X')) {
		c = s[1];
		s += 2;
		base = 16;
	}
	if (base == 0)
		base = c == '0' ? 8 : 10;
	cutoff = (unsigned long)ULONG_MAX / (unsigned long)base;
	cutlim = (unsigned long)ULONG_MAX % (unsigned long)base;
	for (acc = 0, any = 0;; c = *s++) {
		if (isdigit(c))
			c -= '0';
		else if (isalpha(c))
			c -= isupper(c) ? 'A' - 10 : 'a' - 10;
		else
			break;
		if (c >= base)
			break;
		if (any < 0 || acc > cutoff || (acc == cutoff && c > cutlim))
			any = -1;
		else {
			any = 1;
			acc *= base;
			acc += c;
		}
	}
	if (any < 0) {
		acc = ULONG_MAX;
	} else if (neg)
		acc = -acc;
	if (endptr != 0)
		*((const char **)endptr) = any ? s - 1 : nptr;
	return (acc);
}


const char* cmdline_get_option_val(const cmdline_option_t *options,
                                   char vals[][MAX_VALUE_LEN],
                                   const char *opt_name)
{
    int i;
    for ( i = 0; options[i].name != NULL; i++ ) {
        if ( strcmp(options[i].name, opt_name) == 0 )
            return vals[i];
    }
    _XDPRINTF_("requested unknown option: %s\n", opt_name);
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












/*
 * copy of original command line
 * part of tboot measurement (hence in .text section)
 * FIXME - is this getting measured?
 */
char g_cmdline[MAX_CMDLINE_SIZE] = { 0 };

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
    { NULL, NULL }
};

static const cmdline_option_t g_linux_cmdline_options[] = {
    { "vga", "" },
    { "mem", "" },
    { NULL, NULL }
};
/* static char g_linux_param_values[ARRAY_SIZE(g_linux_cmdline_options)][MAX_VALUE_LEN]; */
static char g_tboot_param_values[ARRAY_SIZE(g_tboot_cmdline_options)][MAX_VALUE_LEN];


void tboot_parse_cmdline(void)
{
    cmdline_parse(g_cmdline, g_tboot_cmdline_options, g_tboot_param_values);
}


#if defined (__DEBUG_SERIAL__)

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
    g_uart_config.baud = cmdline_strtoul(com, &com, 10);
    if ( (g_uart_config.baud < 1200) ||
         (g_uart_config.baud > 115200) )
        return false;

    /* parse clock hz */
    if ( *com == '/' ) {
        ++com;
        g_uart_config.clock_hz = cmdline_strtoul(com, &com, 0) << 4;
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
    g_uart_config.port = cmdline_strtoul(com, &com, 0);
    if ( g_uart_config.port == 0 )
        return false;

    /* we don't handle additional params */
    if ( *com == ',' ) {
        return false;
    }


 exit:
    return true;
}

bool get_tboot_serial(void)
{
    const char *serial = cmdline_get_option_val(g_tboot_cmdline_options,
                                        g_tboot_param_values, "serial");
    if ( serial == NULL || *serial == '\0' )
        return false;

    return parse_serial_param(serial);
}

#endif

