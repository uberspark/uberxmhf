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

// printf and friends 
// Adapted from Linux kernel sources and Xen sources for 
// SecVisor by Elaine Shi and Arvind Seshadri
// modified extensively by Amit Vasudevan (amitvasudevan@acm.org)
// for EMHF

#include <emhf.h> 

uint8_t g_log_targets=LOG_TARGET_NONE;
uint8_t g_log_level=LOG_LEVEL_NONE;

/*unsigned char g_dbg_ctype[] = {
_C,_C,_C,_C,_C,_C,_C,_C,                        // 0-7 
_C,_C|_S,_C|_S,_C|_S,_C|_S,_C|_S,_C,_C,         // 8-15 
_C,_C,_C,_C,_C,_C,_C,_C,                        // 16-23 
_C,_C,_C,_C,_C,_C,_C,_C,                        // 24-31 
_S|_SP,_P,_P,_P,_P,_P,_P,_P,                    // 32-39 
_P,_P,_P,_P,_P,_P,_P,_P,                        // 40-47 
_D,_D,_D,_D,_D,_D,_D,_D,                        // 48-55 
_D,_D,_P,_P,_P,_P,_P,_P,                        // 56-63 
_P,_U|_X,_U|_X,_U|_X,_U|_X,_U|_X,_U|_X,_U,      // 64-71 
_U,_U,_U,_U,_U,_U,_U,_U,                        // 72-79 
_U,_U,_U,_U,_U,_U,_U,_U,                        // 80-87 
_U,_U,_U,_P,_P,_P,_P,_P,                        // 88-95 
_P,_L|_X,_L|_X,_L|_X,_L|_X,_L|_X,_L|_X,_L,      // 96-103 
_L,_L,_L,_L,_L,_L,_L,_L,                        // 104-111 
_L,_L,_L,_L,_L,_L,_L,_L,                        // 112-119 
_L,_L,_L,_P,_P,_P,_P,_C,                        // 120-127 
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,                // 128-143 
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,                // 144-159 
_S|_SP,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,   // 160-175 
_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,_P,       // 176-191 
_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,_U,       // 192-207 
_U,_U,_U,_U,_U,_U,_U,_P,_U,_U,_U,_U,_U,_U,_U,_L,       // 208-223 
_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,_L,       // 224-239 
_L,_L,_L,_L,_L,_L,_L,_P,_L,_L,_L,_L,_L,_L,_L,_L};      // 240-255 
*/

static volatile u32 printf_lock=1;
static char printk_prefix[16] = "";

static int skip_atoi(const char **s)
{
    int i=0;

    while (isdigit(**s))
        i = i*10 + *((*s)++) - '0';
    return i;
}


static char * number(char * buf, char * end, unsigned long long num, int base, int size, int precision, int type)
{
    char c,sign,tmp[66];
    const char *digits;
    const char small_digits[] = "0123456789abcdefghijklmnopqrstuvwxyz";
    const char large_digits[] = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    int i, temp;

    digits = (type & LARGE) ? large_digits : small_digits;
    if (type & LEFT)
        type &= ~ZEROPAD;
    if (base < 2 || base > 36)
        return NULL;
    temp = (type & ZEROPAD) ? '0' : ' ';
    c = (char)temp;
    sign = 0;
    if (type & SIGN) {
        if ((signed long long) num < 0) {
            sign = '-';
            num = - (signed long long) num;
            size--;
        } else if (type & PLUS) {
            sign = '+';
            size--;
        } else if (type & SPACE) {
            sign = ' ';
            size--;
        }
    }
    if (type & SPECIAL) {
        if (base == 16)
            size -= 2;
        else if (base == 8)
            size--;
    }
    i = 0;
    if (num == 0)
        tmp[i++]='0';
    else while (num != 0)
        tmp[i++] = digits[do_div(num,base)];
#if 0
    else 
    {
        /* XXX KAF: force unsigned mod and div. */
        unsigned long long num2=(unsigned long long)num;
        unsigned int base2=(unsigned int)base;
        while (num2 != 0) { tmp[i++] = digits[num2%base2]; num2 /= base2; }
    }
#endif
    if (i > precision)
        precision = i;
    size -= precision;
    if (!(type&(ZEROPAD+LEFT))) {
        while(size-->0) {
            if (buf <= end)
                *buf = ' ';
            ++buf;
        }
    }
    if (sign) {
        if (buf <= end)
            *buf = sign;
        ++buf;
    }
    if (type & SPECIAL) {
        if (base==8) {
            if (buf <= end)
                *buf = '0';
            ++buf;
        } else if (base==16) {
            if (buf <= end)
                *buf = '0';
            ++buf;
            if (buf <= end)
                *buf = digits[33];
            ++buf;
        }
    }
    if (!(type & LEFT)) {
        while (size-- > 0) {
            if (buf <= end)
                *buf = c;
            ++buf;
        }
    }
    while (i < precision--) {
        if (buf <= end)
            *buf = '0';
        ++buf;
    }
    while (i-- > 0) {
        if (buf <= end)
            *buf = tmp[i];
        ++buf;
    }
    while (size-- > 0) {
        if (buf <= end)
            *buf = ' ';
        ++buf;
    }
    return buf;
}

/**
 * vsnprintf - Format a string and place it in a buffer
 * @buf: The buffer to place the result into
 * @size: The size of the buffer, including the trailing null space
 * @fmt: The format string to use
 * @args: Arguments for the format string
 *
 * The return value is the number of characters which would
 * be generated for the given input, excluding the trailing
 * '\0', as per ISO C99. If you want to have the exact
 * number of characters written into @buf as return value
 * (not including the trailing '\0'), use vscnprintf. If the
 * return is greater than or equal to @size, the resulting
 * string is truncated.
 *
 * Call this function if you are already dealing with a va_list.
 * You probably want snprintf instead.
 */
static int vsnprintf(char *buf, size_t size, const char *fmt, va_list args)
{
    int len;
    unsigned long long num;
    u32 temp;
    int i, base;
    char *str, *end, c;
    const char *s;

    int flags;          /* flags to number() */

    int field_width;    /* width of output field */
    int precision;              /* min. # of digits for integers; max
                                   number of chars for from string */
    int qualifier;              /* 'h', 'l', or 'L' for integer fields */
                                /* 'z' support added 23/7/1999 S.H.    */
                                /* 'z' changed to 'Z' --davidm 1/25/99 */

    /* Reject out-of-range values early */
    if ((int)size < 0)
      return 0;

    str = buf;
    end = buf + size - 1;

    if (end < buf - 1) {
        end = ((void *) -1);
        size = end - buf + 1;
    }

    for (; *fmt ; ++fmt) {
        if (*fmt != '%') {
            if (str <= end)
                *str = *fmt;
            ++str;
            continue;
        }

    {
      u32 repeat = 1;
      /* process flags */
      flags = 0;
      while (repeat)
      { 
        ++fmt;          /* this also skips first '%' */
        switch (*fmt) {
        case '-': flags |= LEFT; break;
        case '+': flags |= PLUS; break;
        case ' ': flags |= SPACE; break;
        case '#': flags |= SPECIAL; break;
        case '0': flags |= ZEROPAD; break;
        default: repeat = 0; break;
        }
      }
    }

        /* get field width */
        field_width = -1;
        if (isdigit(*fmt))
            field_width = skip_atoi(&fmt);
        else if (*fmt == '*') {
            ++fmt;
            /* it's the next argument */
            field_width = va_arg(args, int);
            if (field_width < 0) {
                field_width = -field_width;
                flags |= LEFT;
            }
        }

        /* get the precision */
        precision = -1;
        if (*fmt == '.') {
            ++fmt;
            if (isdigit(*fmt))
                precision = skip_atoi(&fmt);
            else if (*fmt == '*') {
                ++fmt;
                          /* it's the next argument */
                precision = va_arg(args, int);
            }
            if (precision < 0)
                precision = 0;
        }

        /* get the conversion qualifier */
        qualifier = -1;
        if (*fmt == 'h' || *fmt == 'l' || *fmt == 'L' ||
            *fmt =='Z' || *fmt == 'z') {
            qualifier = *fmt;
            ++fmt;
            if (qualifier == 'l' && *fmt == 'l') {
                qualifier = 'L';
                ++fmt;
            }
        }

        /* default base */
        base = 10;

        switch (*fmt) {
        case 'c':
            if (!(flags & LEFT)) {
                while (--field_width > 0) {
                    if (str <= end)
                        *str = ' ';
                    ++str;
                }
            }
            c = (unsigned char) va_arg(args, int);
            if (str <= end)
                *str = c;
            ++str;
            while (--field_width > 0) {
                if (str <= end)
                    *str = ' ';
                ++str;
            }
            continue;

        case 's':
            s = va_arg(args, char *);
            if ((unsigned long)s < 4096)
                s = "<NULL>";

            len = strnlen(s, (u32)precision);

            if (!(flags & LEFT)) {
                while (len < field_width--) {
                    if (str <= end)
                        *str = ' ';
                    ++str;
                }
            }
            for (i = 0; i < len; ++i) {
                if (str <= end)
                    *str = *s;
                ++str; ++s;
            }
            while (len < field_width--) {
                if (str <= end)
                    *str = ' ';
                ++str;
            }
            continue;

        case 'p':
            if (field_width == -1) {
                field_width = 2*sizeof(void *);
                flags |= ZEROPAD;
            }

	    temp = (u32)va_arg(args, void*);
	    str = number(str, end,
                         (unsigned long long) temp,
                         16, field_width, precision, flags);
            continue;


        case 'n':
            /* FIXME:
             * What does C99 say about the overflow case here? */
            if (qualifier == 'l') {
                long * ip = va_arg(args, long *);
                *ip = (str - buf);
            } else if (qualifier == 'Z' || qualifier == 'z') {
                size_t * ip = va_arg(args, size_t *);
                *ip = (str - buf);
            } else {
                int * ip = va_arg(args, int *);
                *ip = (str - buf);
            }
            continue;

        case '%':
            if (str <= end)
                *str = '%';
            ++str;
            continue;

                        /* integer number formats - set up the flags and "break" */
        case 'o':
            base = 8;
            break;

        case 'X':
            flags |= LARGE;
        case 'x':
            base = 16;
            break;

        case 'd':
        case 'i':
            flags |= SIGN;
        case 'u':
            break;

        default:
            if (str <= end)
                *str = '%';
            ++str;
            if (*fmt) {
                if (str <= end)
                    *str = *fmt;
                ++str;
            } else {
                --fmt;
            }
            continue;
        }
        if (qualifier == 'L')
            num = va_arg(args, long long);
        else if (qualifier == 'l') {
            num = va_arg(args, unsigned long);
            if (flags & SIGN)
                num = (signed long) num;
        } else if (qualifier == 'Z' || qualifier == 'z') {
            num = va_arg(args, size_t);
        } else if (qualifier == 'h') {
            num = (unsigned short) va_arg(args, int);
            if (flags & SIGN)
                num = (signed short) num;
        } else {
            num = va_arg(args, unsigned int);
            if (flags & SIGN)
                num = (signed int) num;
        }

        str = number(str, end, num, base,
                     field_width, precision, flags);
    }
    if (str <= end)
        *str = '\0';
    else if (size > 0)
        /* don't write out a null byte if the buf size is zero */
        *end = '\0';
    /* the trailing null byte doesn't count towards the total
     * ++str;
     */
    return str-buf;
}


#ifdef __DEBUG_SERIAL__
static void vprintf(const char *fmt, va_list args)
{
    int    start_of_line = 1;
    char   _p_buf[1024];

    char         *p, *q;

    (void)vsnprintf(_p_buf, sizeof(_p_buf), fmt, args);

    spin_lock(&printf_lock);

    p = _p_buf;
    while ( (q = strchr(p, '\n')) != NULL )
    {
        *q = '\0';
        if ( start_of_line )
	  emhf_debug_arch_putstr(printk_prefix);
	emhf_debug_arch_putstr(p);
        emhf_debug_arch_putstr("\n");
        start_of_line = 1;
        p = q + 1;
    }

    if ( *p != '\0' )
    {
        if ( start_of_line )
	  emhf_debug_arch_putstr(printk_prefix);
        emhf_debug_arch_putstr(p);
        start_of_line = 0;
    }

    spin_unlock(&printf_lock);
}

void printf(const char *fmt, ...)
{
    va_list       args;

    va_start(args, fmt);
    vprintf(fmt, args);
    va_end(args);        
}

void dprintf(u32 log_type, const char *fmt, ...)
{
    va_list       args;

    if (log_type & ENABLED_LOG_TYPES) {
      va_start(args, fmt);
      vprintf(fmt, args);
      va_end(args);
    }
}

/*
 * if 'prefix' != NULL, print it before each line of hex string
 */
void print_hex(const char *prefix, const void *prtptr, size_t size)
{
    size_t i;
    for ( i = 0; i < size; i++ ) {
        if ( i % 16 == 0 && prefix != NULL )
            printf("\n%s", prefix);
        printf("%02x ", *(const uint8_t *)prtptr++);
    }
    printf("\n");
}

#endif

void emhf_debug_init(char *params){
	emhf_debug_arch_init(params);
}

