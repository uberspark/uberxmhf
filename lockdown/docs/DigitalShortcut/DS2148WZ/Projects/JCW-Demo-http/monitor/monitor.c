//
//  $Id: monitor.c 82 2008-10-06 01:51:43Z jcw $
//  $Revision: 82 $
//  $Author: jcw $
//  $Date: 2008-10-05 21:51:43 -0400 (Sun, 05 Oct 2008) $
//  $HeadURL: http://tinymicros.com/svn_public/arm/lpc2148_demo/trunk/monitor/monitor.c $
//

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string.h>
#include <ctype.h>
#include <fcntl.h>
#include <time.h>
#include <errno.h>
#include <malloc.h>
#include <sys/time.h>
#include <sys/times.h>

#include "FreeRTOS.h"
#include "task.h"

#include "args.h"
#include "../digi_short/wiz_ds.h"
#include "../digi_short/httpserv.h"

#include "../fatfs/ff.h"
#include "../fiq/fiq.h"
#include "../i2c/eeprom.h"
#include "../i2c/i2c.h"
#include "../main.h"
#include "../timer/timer.h"
#include "../swi/swi.h"
#include "monitor.h"
#include "argsdispatch.h"

//
//
//
typedef struct abortDat_s
{
  unsigned int dummy;
  unsigned int sigil;
  unsigned int count;
  unsigned int type;
  unsigned int pc;
  unsigned int opcode;
  unsigned int cpsr;
  unsigned int lr;
  unsigned int sp;
  unsigned int r0;
  unsigned int r1;
  unsigned int r2;
  unsigned int r3;
  unsigned int r4;
  unsigned int r5;
  unsigned int r6;
  unsigned int r7;
  unsigned int r8;
  unsigned int r9;
  unsigned int r10;
  unsigned int r11;
  unsigned int r12;
  unsigned int stack [8];
}
__attribute__ ((packed)) abortDat_t;

//
//  Prototypes
//
static int monitorHelp (int argc, portCHAR **argv);
static int monitorMd (int argc, portCHAR **argv);
static int monitorAbortRegs (int argc, portCHAR **argv);
static int monitorAbortClear (int argc, portCHAR **argv);
static int monitorAbortDirty (int argc, portCHAR **argv);
static int monitorAbortUndef (int argc, portCHAR **argv);
static int monitorAbortPabort (int argc, portCHAR **argv);
static int monitorAbortDabort (int argc, portCHAR **argv);
static int monitorBeepOff (int argc, portCHAR **argv);
static int monitorBeepOn (int argc, portCHAR **argv);
static int monitorBeepMHALL (int argc, portCHAR **argv);
static int monitorBeepSMOTW (int argc, portCHAR **argv);
static int monitorEEAddr (int argc, portCHAR **argv);
static int monitorEERead (int argc, portCHAR **argv);
static int monitorEEReadAddr (int argc, portCHAR **argv);
static int monitorEEWrite (int argc, portCHAR **argv);
static int monitorEEWriteAddr (int argc, portCHAR **argv);
static int monitorEEFillAddr (int argc, portCHAR **argv);
static int monitorI2CRead (int argc, portCHAR **argv);
static int monitorI2CWrite (int argc, portCHAR **argv);
static int monitorI2CWriteRead (int argc, portCHAR **argv);
static int monitorI2CDump (int argc, portCHAR **argv);
static int monitorI2CErrno (int argc, portCHAR **argv);
static int monitorMemTask (int argc, portCHAR **argv);
static int monitorMemMap (int argc, portCHAR **argv);
static int monitorMemAlloc (int argc, portCHAR **argv);
static int monitorMemRealloc (int argc, portCHAR **argv);
static int monitorMemFree (int argc, portCHAR **argv);
static int monitorMemList (int argc, portCHAR **argv);
static int monitorMiscPorts (int argc, portCHAR **argv);
static int monitorMiscSizeof (int argc, portCHAR **argv);
static int monitorVersion (int argc, portCHAR **argv);
static int monitorWizInfo (int argc, portCHAR **argv);
static int monitorListLog (int argc, portCHAR **argv);

//
//  Ye olde globals
//
static const commandList_t commandListAbort [] =
{
  { "help",     0,  0, CMDTYPE_FUNCTION,  { monitorHelp        }, "This help list",                 "'help' has no parameters" },
  { "regs",     0,  0, CMDTYPE_FUNCTION,  { monitorAbortRegs   }, "Print abort registers",          "'regs' has no parameters" },
  { "clear",    0,  0, CMDTYPE_FUNCTION,  { monitorAbortClear  }, "Clear abort registers",          "'clear' has no parameters" },
  { "dirty",    0,  0, CMDTYPE_FUNCTION,  { monitorAbortDirty  }, "Dirty sigil flag",               "'dirty' has no parameters" },
  { "undef",    0,  0, CMDTYPE_FUNCTION,  { monitorAbortUndef  }, "Execute undefined instruction",  "'undef' has no parameters" },
  { "pabort",   0,  0, CMDTYPE_FUNCTION,  { monitorAbortPabort }, "Cause prefetch abort",           "'pabort' has no parameters" },
  { "dabort",   0,  0, CMDTYPE_FUNCTION,  { monitorAbortDabort }, "Cause data abort",               "'dabort' has no parameters" },
  { NULL,       0,  0, CMDTYPE_FUNCTION,  { NULL               }, NULL,                             NULL },
};

static const commandList_t commandListBeep [] =
{
  { "off",      0,  0, CMDTYPE_FUNCTION,  { monitorBeepOff     }, "Turn beeper off",              "'off' has no parameters" },
  { "on",       1,  1, CMDTYPE_FUNCTION,  { monitorBeepOn      }, "Start <hz> frequency beep",    "'on [60..20000]'" },
  { "mhall",    0,  0, CMDTYPE_FUNCTION,  { monitorBeepMHALL   }, "Play Mary Had a Little Lamb",  "'mhall' has no parameters" },
  { "smotw",    0,  0, CMDTYPE_FUNCTION,  { monitorBeepSMOTW   }, "Play Smoke On The Water",      "'smotw' has no parameters" },
  { NULL,       0,  0, CMDTYPE_FUNCTION,  { NULL               }, NULL,                           NULL },
};

static const commandList_t commandListEE [] =
{
  { "help",     0,  0, CMDTYPE_FUNCTION,  { monitorHelp        }, "This help list",               "'help' has no parameters" },
  { "a",        1,  1, CMDTYPE_FUNCTION,  { monitorEEAddr      }, "Set eeprom r/w address",       "'ee <address>'" },
  { "r",        0,  1, CMDTYPE_FUNCTION,  { monitorEERead      }, "Read from current address",    "'r <# bytes>'" },
  { "ra",       1,  2, CMDTYPE_FUNCTION,  { monitorEEReadAddr  }, "Read EEPROM",                  "'ra <address> <# bytes>'" },
  { "w",        1, 16, CMDTYPE_FUNCTION,  { monitorEEWrite     }, "Write to current address",     "'w <byte> [<byte> [...<byte>]]'" },
  { "wa",       2, 17, CMDTYPE_FUNCTION,  { monitorEEWriteAddr }, "Write EEPOM",                  "'wa <address> <byte> [<byte> [...<byte>]]'" },
  { "fa",       3,  3, CMDTYPE_FUNCTION,  { monitorEEFillAddr  }, "Fill EEPOM",                   "'fa <address> <len> <byte>'" },
  { NULL,       0,  0, CMDTYPE_FUNCTION,  { NULL               }, NULL,                           NULL },
};

static const commandList_t commandListI2C [] =
{
  { "help",     0,  0, CMDTYPE_FUNCTION,  { monitorHelp        }, "This help list",                     "'help' has no parameters" },
  { "r",        2,  2, CMDTYPE_FUNCTION,  { monitorI2CRead     }, "Read from I2C device",               "'r <address> <# bytes>'" },
  { "w",        2, 17, CMDTYPE_FUNCTION,  { monitorI2CWrite    }, "Write to I2C device",                "'w <address> <byte> [<byte> [...<byte>]]'" },
  { "wr",       2, 18, CMDTYPE_FUNCTION,  { monitorI2CWriteRead}, "Write to then read from I2C device", "'wr <address> <byte> [<byte> [...<byte>]] <# bytes to read>'" },
  { "dump",     0,  0, CMDTYPE_FUNCTION,  { monitorI2CDump     }, "Dump I2C Debug Buffer",              "'dump' has no parameters" },
  { "errno",    0,  0, CMDTYPE_FUNCTION,  { monitorI2CErrno    }, "Display i2cErrno value",             "'errno' has no parameters" },
  { NULL,       0,  0, CMDTYPE_FUNCTION,  { NULL               }, NULL,                                 NULL },
};

static const commandList_t commandListMem [] =
{
  { "help",     0,  0, CMDTYPE_FUNCTION,  { monitorHelp        }, "This help list",               "'help' has no parameters" },
  { "task",     0,  0, CMDTYPE_FUNCTION,  { monitorMemTask     }, "Show FreeRTOS task memory",    "'task' has no parameters" },
  { "map",      0,  0, CMDTYPE_FUNCTION,  { monitorMemMap      }, "Show various addresses",       "'map' has no parameters" },
  { "alloc",    2,  2, CMDTYPE_FUNCTION,  { monitorMemAlloc    }, "Allocate memory",              "'alloc <slot> <size>'" },
  { "realloc",  2,  2, CMDTYPE_FUNCTION,  { monitorMemRealloc  }, "Reallocate memory",            "'realloc <slot> <size>'" },
  { "free",     1,  1, CMDTYPE_FUNCTION,  { monitorMemFree     }, "Free memory",                  "'free <slot>'" },
  { "list",     0,  0, CMDTYPE_FUNCTION,  { monitorMemList     }, "List memory",                  "'list' has no parameters" },
  { NULL,       0,  0, CMDTYPE_FUNCTION,  { NULL               }, NULL,                           NULL },
};

static const commandList_t commandListMisc [] =
{
  { "help",     0,  0, CMDTYPE_FUNCTION,  { monitorHelp        }, "This help list",               "'help' has no parameters" },
  { "ports",    0,  0, CMDTYPE_FUNCTION,  { monitorMiscPorts   }, "Display port registers",       "'ports' has no parameters" },
  { "sizeof",   0,  0, CMDTYPE_FUNCTION,  { monitorMiscSizeof  }, "Sizeof() variable data types", "'sizeof' has no parameters" },
  { NULL,       0,  0, CMDTYPE_FUNCTION,  { NULL               }, NULL,                           NULL },
};

static const commandList_t commandList [] =
{
  { "help",     0,  0, CMDTYPE_FUNCTION,  { monitorHelp        }, "This help list",                 "'help' has no parameters" },
  { "abort",    1,  0, CMDTYPE_CMDLIST,   { commandListAbort   }, "Read/clear abort registers",     "'abort help' for help list" },
  { "beep",     0,  1, CMDTYPE_CMDLIST,   { commandListBeep    }, "Beep related functions",         "'beep help' for help list" },
  { "ee",       1,  0, CMDTYPE_CMDLIST,   { commandListEE      }, "Read/write I2C EEPROM",          "'ee help' for help list" },
  { "i2c",      1,  0, CMDTYPE_CMDLIST,   { commandListI2C     }, "Perform I2C commands",           "'i2c help' for help list" },
  { "md",       0,  2, CMDTYPE_FUNCTION,  { monitorMd          }, "Display memory",                 "'md [address [length]]'" },
  { "mem",      1,  0, CMDTYPE_CMDLIST,   { commandListMem     }, "Various memory functions",       "'mem help' for help list" },
  { "misc",     1,  0, CMDTYPE_CMDLIST,   { commandListMisc    }, "Miscellaneous stuff",            "'misc help' for help list" },
  { "ver",  		0,  0, CMDTYPE_FUNCTION,  { monitorVersion     }, "Display version info",    				"'version' has no parameters" },
  { "wiz",  		0,  0, CMDTYPE_FUNCTION,  { monitorWizInfo     }, "Display Wiznet info",    				"'wiz' has no parameters" },
  { "log",  		0,  0, CMDTYPE_FUNCTION,  { monitorListLog     }, "Display DS Log", 			   				"'log' has no parameters" },
  { NULL,       0,  0, CMDTYPE_FUNCTION,  { NULL               }, NULL,                             NULL },
};

commandList_t *activeCommandList = NULL;

//
//  External variables
//
extern unsigned int __abort_dat;
extern unsigned long __start_of_text__;
extern unsigned long __end_of_text__;
extern unsigned long __start_of_startup__;
extern unsigned long __end_of_startup__;
extern unsigned long __start_of_prog__;
extern unsigned long __end_of_prog__;
extern unsigned long __start_of_rodata__;
extern unsigned long __end_of_rodata__;
extern unsigned long __start_of_glue7__;
extern unsigned long __end_of_glue7__;
extern unsigned long __data_beg__;
extern unsigned long __data_end__;
extern unsigned long __bss_beg__;
extern unsigned long __bss_end__;
extern unsigned long __heap_max;
extern unsigned long __heap_beg;
extern unsigned long __heap_end;
extern unsigned long __stack_end__;
extern unsigned long __stack_beg_und;
extern unsigned long __stack_end_und;
extern unsigned long __stack_beg_abt;
extern unsigned long __stack_end_abt;
extern unsigned long __stack_beg_fiq;
extern unsigned long __stack_end_fiq;
extern unsigned long __stack_beg_irq;
extern unsigned long __stack_end_irq;
extern unsigned long __stack_beg_svc;
extern unsigned long __stack_end_svc;
extern unsigned long __stack_beg_sys;
extern unsigned long __stack_end_sys;

//
//  These two really ought to be in the FatFS code
//
U32 get_fattime ()
{
  U32 tmr;
  time_t now;
  struct tm tm;

  now = time (NULL);
  localtime_r (&now, &tm);

  tmr = 0
    | ((tm.tm_year - 80) << 25)
    | ((tm.tm_mon + 1)   << 21)
    | (tm.tm_mday        << 16)
    | (tm.tm_hour        << 11)
    | (tm.tm_min         << 5)
    | (tm.tm_sec         >> 1);

  return tmr;
}

//
//  Functions newlib doesn't know about (but should)
//
void _sync  (void);
int  _mkdir (const char *path, mode_t mode);
int  _chmod (const char *path, mode_t mode);

void sync  (void);
int  chmod (const char *path, mode_t mode);

void sync (void)
{
  _sync ();
}

int mkdir (const char *path, mode_t mode)
{
  return _mkdir (path, mode);
}

int chmod (const char *path, mode_t mode)
{
  return _chmod (path, mode);
}

//
//
//
static int getNumber (char *s, unsigned int *result)
{
  unsigned int value;
  unsigned int mustBeHex = FALSE;
  int sgn = 1;
  const unsigned char hexToDec [] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 255, 255, 255, 255, 255, 255, 255, 10, 11, 12, 13, 14, 15};

  if (!s)
    return 0;

  if ((strlen (s) > 2) && (!strncmp (s, "0x", 2) || !strncmp (s, "0X", 2)))
  {
    mustBeHex = TRUE;
    s += 2;
  }

  if (!mustBeHex && *s && (*s == '-'))
  {
    sgn = -1;
    s++;
  }

  for (value = 0; *s; s++)
  {
    if (mustBeHex && isxdigit (*s))
      value = (value << 4) | hexToDec [toupper (*s) - '0'];
    else if (isdigit (*s))
      value = (value * 10) + (*s - '0');
    else
    {
      printf ("Malformed number.  Must be decimal number, or hex value preceeded by '0x'\n");
      return 0;
    }
  }

  if (!mustBeHex)
    value *= sgn;

  *result = value;

  return 1;
}

static int monitorDumpMemory (unsigned int displayAddress, unsigned int address, int length)
{
  unsigned char *buffer;
  int i;

  if (!length)
  {
    printf ("Error: monitorDumpMemory() passed 0 for length\n");
    return address;
  }

  for (buffer = (unsigned char *) address, i = 0; i < length; i += 16)
  {
    unsigned int l;
    unsigned int j;

    if (i)
      printf ("\n");

    printf ("%08x: ", displayAddress + i);

    if ((length - i) < 16)
      l = length & 15;
    else
      l = 16;

    for (j = 0; j < 16; j++)
    {
      if (j < l)
        printf ("%02x ", buffer [i+j]);
      else
        printf ("   ");
    }

    printf ("  ");

    for (j = 0; j < l; j++)
    {
      unsigned char c = buffer [i+j];

      if (c < 32 || c > 127)
        c = '.';

      printf ("%c", c);
    }
  }

  printf ("\n");

  address += length;

  return address;
}

//
//
//
static int monitorHelp (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  unsigned int i;
  int t;
  int longestCmd;
  portCHAR spaces [32];

  memset (spaces, ' ', sizeof (spaces));

  for (longestCmd = 0, i = 0; activeCommandList [i].command; i++)
    if ((t = strlen (activeCommandList [i].command)) > longestCmd)
      longestCmd = t;

  spaces [longestCmd] = '\0';

  for (i = 0; activeCommandList [i].command; i++)
  {
    const commandList_t *cl = &activeCommandList [i];

    printf ("%s%s -- %s\n", cl->command, &spaces [strlen (cl->command)], cl->description);
  }

  printf ("\nUse '<command> ?' for details on parameters to command\n");

  return 0;
}

//
//
//
static int monitorMd (int argc, portCHAR **argv)
{
  static unsigned int address = 0x00000000;
  unsigned int length = 256;

  if ((argc >= 1))
  {
    if (!getNumber (argv [0], &address))
      return 0;

    if (argc == 2)
      if (!getNumber (argv [1], &length))
        return 0;
  }

  address = monitorDumpMemory (address, address, length);

  return 0;
}

//
//
//
static int monitorAbortRegs (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  abortDat_t *ad = (abortDat_t *) &__abort_dat;

  printf ("contents=%s, sigil=0x%08x, count=%d\n", (ad->sigil == 0xdeadc0de) ? "probable" : "invalid", ad->sigil, ad->count);
  printf ("abort type=%s\n", (ad->type == 0) ? "undefined instruction" : (ad->type == 1) ? "prefetch abort" : (ad->type == 2) ? "data abort" : "unknown");
  printf ("pc=0x%08x, opcode=0x%08x\n", ad->pc, ad->opcode);
  printf ("cpsr=0x%08x, sp=0x%08x, lr=0x%08x\n", ad->cpsr, ad->sp, ad->lr);
  printf ("r0=0x%08x, r1=0x%08x, r2=0x%08x, r3=0x%08x\n", ad->r0, ad->r1, ad->r2, ad->r3);
  printf ("r4=0x%08x, r5=0x%08x, r6=0x%08x, r7=0x%08x\n", ad->r4, ad->r5, ad->r6, ad->r7);
  printf ("r8=0x%08x, r9=0x%08x, r10=0x%08x, r11=0x%08x\n", ad->r8, ad->r9, ad->r10, ad->r11);
  printf ("r12=0x%08x\n", ad->r12);
  printf ("\n");

  printf ("sp[0]=0x%08x, sp[1]=0x%08x, sp[2]=0x%08x, sp[3]=0x%08x\n", ad->stack [0], ad->stack [1], ad->stack [2], ad->stack [3]);
  printf ("sp[4]=0x%08x, sp[5]=0x%08x, sp[6]=0x%08x, sp[7]=0x%08x\n", ad->stack [4], ad->stack [5], ad->stack [6], ad->stack [7]);

  return 0;
}

static int monitorAbortClear (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  abortDat_t *ad = (abortDat_t *) &__abort_dat;

  memset (ad, 0, sizeof (* ad));

  return 0;
}

static int monitorAbortDirty (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  abortDat_t *ad = (abortDat_t *) &__abort_dat;

  ad->sigil = 0;

  return 0;
}

static int monitorAbortUndef (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  asm volatile (" .word 0x06000010" : /* no output */ : /* no inputs */ );

  return 0;
}

static int monitorAbortPabort (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  asm volatile (" ldr r0, =0x00080000" : /* no output */ : /* no inputs */ );
  asm volatile (" mov pc, r0" : /* no output */ : /* no inputs */ );

  return 0;
}

static int monitorAbortDabort (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  unsigned char c;
  volatile unsigned char *ptr = (unsigned char *) 0x40008000;

  c = *ptr;

  return 0;
}

//
//
//
static int monitorBeepOff (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  timerBeepOff ();

  return 0;
}

static int monitorBeepOn (int argc __attribute__ ((unused)), portCHAR **argv)
{
  int  hz = atoi (argv [0]);

  if ((hz < 60) || (hz > 20000))
    printf ("Frequency must be between 60 and 20000 Hertz\n");
  else 
    timerBeepOn (hz);

  return 0;
}

static int monitorBeepMHALL (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  timerBeepMHALL ();

  return 0;
}

static int monitorBeepSMOTW (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  timerBeepSMOTW ();

  return 0;
}

//
//
//
static int monitorEEAddr (int argc __attribute__ ((unused)), portCHAR **argv)
{
  unsigned int address;

  if (!getNumber (argv [0], &address))
    return 0;

  if (eepromSetAddress (address))
  {
    printf ("Error: address out of range\n");
    eepromSetAddress (0);
  }

  return 0;
}

static int monitorEERead (int argc, portCHAR **argv)
{
  unsigned int address;
  unsigned int length = 256;
  unsigned char buffer [64];
  unsigned int i;

  if (argc && !getNumber (argv [0], &length))
    return 0;

  for (address = eepromGetAddress(), i = 0; i < length; i += sizeof (buffer), address = (address + sizeof (buffer)) % EEPROM_SIZE)
  {
    unsigned int l;

    if (!(l = i % sizeof (buffer)))
      l = MIN (length, sizeof (buffer));

    if (eepromRead (buffer, l))
    {
      printf ("eepromRead() returned error %d/%s\n", i2cGetErrno (), i2cStrerror (i2cGetErrno ()));
      return 0;
    }

    monitorDumpMemory (address, (unsigned int) buffer, l);
  }

  return 0;
}

static int monitorEEReadAddr (int argc, portCHAR **argv)
{
  unsigned int address;
  
  if (!getNumber (argv [0], &address))
    return 0;

  if (eepromSetAddress (address))
  {
    printf ("Error: address out of range\n");
    return 0;
  }

  return monitorEERead (--argc, ++argv);
}

static int monitorEEWriteCommon (int argc, portCHAR **argv, unsigned char *buffer, int bufferLength)
{
  int i;

  for (i = 0; i < argc; i++)
  {
    unsigned int n;

    if (i >= bufferLength)
    {
      printf ("Error: buffer too small for number arguments\n");
      return -1;
    }

    if (!getNumber (argv [i], &n))
      return 0;

    if (n > 255)
    {
      printf ("Error: data must be 0x00..0xff (0..255)\n");
      return -1;
    }

    buffer [i] = n;
  }

  return 0;
}

//
//  Note the two reserved bytes at the beginning of the buffer.  These are
//  reserved for the address we're writing to in the EEPROM.  They're populated
//  by the eepromWrite() routine.  This feel hackish, but unlike the read
//  routines, we can't send the address, then a repeated start bit to switch to
//  write.
//
static int monitorEEWrite (int argc, portCHAR **argv)
{
  unsigned char buffer [18];

  if (monitorEEWriteCommon (argc, argv, &buffer [2], sizeof (buffer) - 2))
    return 0;

  if (eepromWrite (buffer, argc))
    printf ("eepromWrite() returned %d/%s\n", i2cGetErrno (), i2cStrerror (i2cGetErrno ()));

  return 0;
}

static int monitorEEWriteAddr (int argc, portCHAR **argv)
{
  unsigned int address;

  if (!getNumber (argv [0], &address))
    return 0;

  if (eepromSetAddress (address))
  {
    printf ("Error: address out of range\n");
    return 0;
  }

  return monitorEEWrite (--argc, ++argv);
}

static int monitorEEFillAddr (int argc __attribute__ ((unused)), portCHAR **argv)
{
  unsigned int address;
  unsigned int length;
  unsigned int fillChar;

  if (!getNumber (argv [0], &address) || !getNumber (argv [1], &length) || !getNumber (argv [2], &fillChar))
    return 0;

  if (fillChar > 255)
    printf ("Error: fill value must be 0x00..0xff (0..255)\n");
  else if (eepromFillAddress (address, length, fillChar))
    printf ("eepromFillAddress() returned error %d/%s\n", i2cGetErrno (), i2cStrerror (i2cGetErrno ()));

  return 0;
}




int monitorTimevalSubtract (struct timeval *result, struct timeval *x, struct timeval *y);
int monitorTimevalSubtract (struct timeval *result, struct timeval *x, struct timeval *y)
{
  if (x->tv_usec < y->tv_usec)
  {
    int nsec = (y->tv_usec - x->tv_usec) / 1000000 + 1;
    y->tv_usec -= 1000000 * nsec;
    y->tv_sec += nsec;
  }

  if (x->tv_usec - y->tv_usec > 1000000)
  {
    int nsec = (x->tv_usec - y->tv_usec) / 1000000;
    y->tv_usec += 1000000 * nsec;
    y->tv_sec -= nsec;
  }

  result->tv_sec = x->tv_sec - y->tv_sec;
  result->tv_usec = x->tv_usec - y->tv_usec;

  return x->tv_sec < y->tv_sec;
}

typedef enum
{
  MODE_NORMAL = 0,
  MODE_NOINTS,
  MODE_SUSPENDALL,
  MODE_HIGH
}
mode_e;

//
//
//
int monitorI2CRead (int argc __attribute__ ((unused)), portCHAR **argv)
{
  unsigned int address;
  unsigned int numBytes;
  unsigned char buffer [16];
  int r;

  if (!getNumber (argv [0], &address))
    return 0;
  if (!getNumber (argv [1], &numBytes))
    return 0;

  if (address > 255)
  {
    printf ("Error: address must be 0x00..0xff (0..255)\n");
    return 0;
  }

  if ((numBytes < 1) || (numBytes > sizeof (buffer)))
  {
    printf ("Error: number of bytes must be 1..%ld\n", sizeof (buffer));
    return 0;
  }

  r = i2cReadBuffer (address, buffer, numBytes);

  printf ("i2cReadBuffer() returned %d/%s (%s)\n\n", i2cGetErrno (), i2cStrerror (i2cGetErrno ()), r ? "error" : "no error");

  monitorDumpMemory (0, (unsigned int) buffer, (int) sizeof (buffer));

  return 0;
}

int monitorI2CWrite (int argc, portCHAR **argv)
{
  unsigned int address;
  unsigned char buffer [16];
  int i;

  if (!getNumber (argv [0], &address))
    return 0;

  if (address > 255)
  {
    printf ("Error: address must be 0x00..0xff (0..255)\n");
    return 0;
  }

  for (i = 0; i < argc - 1; i++)
  {
    unsigned int n;

    if (!getNumber (argv [i + 1], &n))
      return 0;

    if (n > 255)
    {
      printf ("Error: data must be 0x00..0xff (0..255)\n");
      return 0;
    }

    buffer [i] = n;
  }

  i = i2cWriteBuffer (address, buffer, argc - 1);

  printf ("i2cWriteBuffer() returned %d/%s (%s)\n", i2cGetErrno (), i2cStrerror (i2cGetErrno ()), i ? "error" : "no error");

  return 0;
}

int monitorI2CWriteRead (int argc, portCHAR **argv)
{
  unsigned int address;
  unsigned int bytesToWrite;
  unsigned int bytesToRead;
  unsigned char buffer [16];
  unsigned int i;

  if (!getNumber (argv [0], &address))
    return 0;

  if (address > 255)
  {
    printf ("Error: address must be 0x00..0xff (0..255)\n");
    return 0;
  }

  for (bytesToWrite = argc - 2, i = 0; i < bytesToWrite; i++)
  {
    unsigned int n;

    if (!getNumber (argv [i + 1], &n))
      return 0;

    if (n > 255)
    {
      printf ("Error: data must be 0x00..0xff (0..255)\n");
      return 0;
    }

    buffer [i] = n;
  }

  if (!getNumber (argv [argc - 1], &bytesToRead))
    return 0;

  if ((bytesToRead < 1) || (bytesToRead > sizeof (buffer)))
  {
    printf ("Error: number of bytes must be 1..%ld\n", sizeof (buffer));
    return 0;
  }

  i2cWriteReadBuffer (address, buffer, bytesToWrite, bytesToRead);

  printf ("i2cWriteReadBuffer() returned %d/%s\n\n", i2cGetErrno (), i2cStrerror (i2cGetErrno ()));

  monitorDumpMemory (0, (unsigned int) buffer, (int) sizeof (buffer));

  return 0;
}

int monitorI2CDump (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  i2cDump ();

  return 0;
}

int monitorI2CErrno (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  printf ("i2cErrno=%d/%s\n", i2cGetErrno (), i2cStrerror (i2cGetErrno ()));

  return 0;
}



extern xTaskHandle taskHandles [TASKHANDLE_LAST];


static int monitorMemTask (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
#if configUSE_TRACE_FACILITY == 1
  signed portCHAR buffer [TASKHANDLE_LAST * 42];
  int bytesFree;
  int bytesUsed;
  int blocksFree;
  signed portCHAR *s = buffer;

  vTaskList (buffer);
  vPortUsedMem (&bytesFree, &bytesUsed, &blocksFree);

  while ((s = (signed portCHAR *) index ((char *) s, '\r')))
    *s = ' ';

  printf ("Task\t\tState\tPrty\tStack\tTask#\n");
  printf ("%s\nHeap size=%ld, used=%d, free=%d (%d blocks)\n", buffer, configTOTAL_HEAP_SIZE, bytesUsed, bytesFree, blocksFree);
#else
  printf ("Not implemented (requires configUSE_TRACE_FACILITY in FreeRTOSConfig.h)\n");
#endif

  return 0;
}

typedef struct memMap_s
{
  char *desc;
  int m;
  unsigned int start;
  unsigned int end;
}
memMap_t;

typedef union 
{
  void *v;
  unsigned int i;
}
sbrkConv_t;

static inline unsigned __get_cpsr (void)
{
  unsigned long retval;

  asm volatile (" mrs  %0, cpsr" : "=r" (retval) : /* no inputs */  );

  return retval;
}

static int monitorMemMap (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  unsigned int i;
  sbrkConv_t sbrkConv;
  static memMap_t memMap [] = 
  {
    { ".startup .....", 0, (unsigned int) &__start_of_startup__, (unsigned int) &__end_of_startup__ },
    { ".text ........", 0, (unsigned int) &__start_of_text__,    (unsigned int) &__end_of_text__ },
    { ".code ........", 0, (unsigned int) &__start_of_prog__,    (unsigned int) &__end_of_prog__ },
    { ".rodata ......", 0, (unsigned int) &__start_of_rodata__,  (unsigned int) &__end_of_rodata__ },
    { ".data ........", 0, (unsigned int) &__data_beg__,         (unsigned int) &__data_end__ },
    { ".bss .........", 0, (unsigned int) &__bss_beg__,          (unsigned int) &__bss_end__ },
    { "heap .........", 1, (unsigned int) &__heap_beg,           (unsigned int) &__heap_end },
    { "heap range ...", 1, (unsigned int) &__heap_beg,           (unsigned int) &__heap_max },
//  { "SYS stack ....", 1, (unsigned int) &__stack_beg_sys,      (unsigned int) &__stack_end_sys }, // Not relevant to FreeRTOS
    { "SVC stack ....", 1, (unsigned int) &__stack_beg_svc,      (unsigned int) &__stack_end_svc },
    { "IRQ stack ....", 1, (unsigned int) &__stack_beg_irq,      (unsigned int) &__stack_end_irq },
    { "FIQ stack ....", 1, (unsigned int) &__stack_beg_fiq,      (unsigned int) &__stack_end_fiq },
    { "abort stack ..", 1, (unsigned int) &__stack_beg_abt,      (unsigned int) &__stack_end_abt },
    { "undef stack ..", 1, (unsigned int) &__stack_beg_und,      (unsigned int) &__stack_end_und },
  };

  sbrkConv.v = sbrk (0);
  __heap_end = sbrkConv.i;
  __stack_end_sys = sbrkConv.i;

  printf ("Section        Start      End        Length\n");
  printf ("-------------------------------------------\n");

  for (i = 0; i < arrsizeof (memMap); i++)
  {
    if (!memMap [i].m)
      printf ("%s 0x%08x 0x%08x 0x%x\n", memMap [i].desc, memMap [i].start, memMap [i].end, abs (memMap [i].end - memMap [i].start));
    else
      printf ("%s 0x%08x 0x%08x 0x%x\n", memMap [i].desc, *(unsigned int *) memMap [i].start, *(unsigned int *) memMap [i].end, abs (*(unsigned int *) memMap [i].end - *(unsigned int *) memMap [i].start));
  }

#if 0
  printf ("\nProcessor mode ");

  switch ((i = __get_cpsr ()) & 0x1f)
  {
    case 0x10 : printf ("User"); break;
    case 0x11 : printf ("FIQ"); break;
    case 0x12 : printf ("IRQ"); break;
    case 0x13 : printf ("Supervisor"); break;
    case 0x17 : printf ("Abort"); break;
    case 0x1b : printf ("Undefined"); break;
    case 0x1f : printf ("System"); break;
    default   : printf ("Unknown");
  }

  printf (", IRQ %s", (i & 0x80) ? "disabled" : "enabled");
  printf (", FIQ %s", (i & 0x40) ? "disabled" : "enabled");
  printf (", mode %s\n", (i & 0x20) ? "THUMB" : "ARM");
#endif

  printf ("\n");
  malloc_stats ();

  return 0;
}

typedef struct memorySlots_s
{
  unsigned char *p;
  unsigned int size;
}
memorySlots_t;

memorySlots_t memorySlots [8];

static int monitorMemAlloc (int argc __attribute__ ((unused)), portCHAR **argv)
{
  unsigned int size;
  unsigned int slot;
  unsigned char *p;

  if (!getNumber (argv [0], &slot) || !getNumber (argv [0], &size))
    return 0;

  if (slot >= arrsizeof (memorySlots))
  {
    printf ("slot must be 0..%lu\n", arrsizeof (memorySlots) - 1);
    return 0;
  }

  if (memorySlots [slot].p)
    printf ("Slot %d in use, free it first, or use realloc\n", slot);
  else if (!(p = malloc (size)))
    printf ("malloc() failed, error %d/%s\n", errno, strerror (errno));
  else
  {
    memorySlots [slot].p = p;
    memorySlots [slot].size = size;
  }

  return 0;
}

static int monitorMemRealloc (int argc __attribute__ ((unused)), portCHAR **argv)
{
  unsigned int size;
  unsigned int slot;
  unsigned char *p;

  if (!getNumber (argv [0], &slot) || !getNumber (argv [0], &size))
    return 0;

  if (slot >= arrsizeof (memorySlots))
  {
    printf ("slot must be 0..%lu\n", arrsizeof (memorySlots) - 1);
    return 0;
  }

  if (!(p = realloc (memorySlots [slot].p, size)))
    printf ("realloc() failed, error %d/%s\n", errno, strerror (errno));
  else
  {
    memorySlots [slot].p = p;
    memorySlots [slot].size = size;
  }

  return 0;
}

static int monitorMemFree (int argc __attribute__ ((unused)), portCHAR **argv)
{
  unsigned int slot;

  if (!getNumber (argv [0], &slot))
    return 0;

  if (slot >= arrsizeof (memorySlots))
  {
    printf ("slot must be 0..%lu\n", arrsizeof (memorySlots) - 1);
    return 0;
  }

  if (!memorySlots [slot].p)
    printf ("Can't free it, slot %d not in use\n", slot);
  else
  {
    free (memorySlots [slot].p);
    memorySlots [slot].p = NULL;
    memorySlots [slot].size = 0;
  }

  return 0;
}

static int monitorMemList (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  unsigned int i;

  printf ("Slot  Address     Size\n");
  printf ("----------------------\n");

  for (i = 0; i < arrsizeof (memorySlots); i++)
    printf ("%4d  0x%08x  %d\n", i, (unsigned int) memorySlots [i].p, memorySlots [i].size);

  return 0;
}

//
//
//
static int monitorMiscPorts (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  unsigned int gpio0_fiopin;
  unsigned int gpio0_fiodir;
  unsigned int gpio0_fiomask;
  unsigned int gpio1_fiopin;
  unsigned int gpio1_fiodir;
  unsigned int gpio1_fiomask;

  portENTER_CRITICAL ();

  gpio0_fiopin  = GPIO0_FIOPIN;
  gpio0_fiodir  = GPIO0_FIODIR;
  gpio0_fiomask = GPIO0_FIOMASK;
  gpio1_fiopin  = GPIO1_FIOPIN;
  gpio1_fiodir  = GPIO1_FIODIR;
  gpio1_fiomask = GPIO1_FIOMASK;

  portEXIT_CRITICAL ();

  printf ("GPIO0_FIOPIN  = 0x%08x\n", gpio0_fiopin);
  printf ("GPIO0_FIODIR  = 0x%08x\n", gpio0_fiodir);
  printf ("GPIO0_FIOMASK = 0x%08x\n", gpio0_fiomask);
  printf ("GPIO1_FIOPIN  = 0x%08x\n", gpio1_fiopin);
  printf ("GPIO1_FIODIR  = 0x%08x\n", gpio1_fiodir);
  printf ("GPIO1_FIOMASK = 0x%08x\n", gpio1_fiomask);

  return 0;
}

static int monitorMiscSizeof (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  printf ("sizeof (char)      = %lu\n", sizeof (char));
  printf ("sizeof (short)     = %lu\n", sizeof (short));
  printf ("sizeof (int)       = %lu\n", sizeof (int));
  printf ("sizeof (long)      = %lu\n", sizeof (long));
  printf ("sizeof (long long) = %lu\n", sizeof (long long));
  printf ("sizeof (float)     = %lu\n", sizeof (float));
  printf ("sizeof (double)    = %lu\n", sizeof (double));
  printf ("sizeof (void *)    = %lu\n", sizeof (void *));

  return 0;
}

//
//
//
static int monitorVersion (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  printf ("DS-2148 Demo, Version " __VERSION ", " __DATE__ " " __TIME__ "\n");
  printf ("Copyright (c) 2008, J.C. Wren\n");
  printf ("Copyright (c) 2009, Digital Shortcut Inc.\n");

  return 0;
}

static int monitorWizInfo (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
  WizCheck0();
	ShowIPs();
	
  return 0;
}

static int monitorListLog (int argc __attribute__ ((unused)), portCHAR **argv __attribute__ ((unused)))
{
	LogDisplay();
	
  return 0;
}


//
//
//
#if defined CFG_CONSOLE_USB || defined CFG_CONSOLE_UART1
static void monitorReassignFD (FILE *fp, int fd);
static void monitorReassignFD (FILE *fp, int fd)
{
  fp->_file = fd;
}
#endif

portTASK_FUNCTION (vMonitorTask, pvParameters __attribute__ ((unused)))
{
  static U8 buffer [256];
  static portCHAR *argv [34];
  int argc;
  int fd = fileno (stdin);

  fclose (stderr);
  stderr = stdout;

#if defined CFG_CONSOLE_USB
  fd = open ("/dev/usb", O_RDWR);
#elif defined CFG_CONSOLE_UART1
  fd = open ("/dev/uart1", O_RDWR);
#endif

#if defined CFG_CONSOLE_USB || defined CFG_CONSOLE_UART1
  monitorReassignFD (stdin, fd);
  monitorReassignFD (stdout, fd);
#endif

  monitorVersion (0, NULL);

  for (;;)
  {
    int l;

    if ((l = argsGetLine (fd, buffer, sizeof (buffer), "Demo>")))
    {
      if ((l == 1) && ((buffer [0] == 0xfe) || (buffer [0] == 0xff)))
      {
        int type = buffer [0];
        time_t now = time (NULL);
        ctime_r (&now, (char *) buffer);
        printf ("%s -- %s", (type == 0xfe) ? "ALARM" : "PERIODIC", buffer);
      }
      else if (argsParse ((char *) buffer, argv, sizeof (argv), &argc))
        printf ("Too many arguments (max %ld)\n", arrsizeof (argv));
      else if (argv [0])
        argsDispatch (commandList, argc, &argv [0]);
    }

    WD_FEED = WD_FEED_FEED1;
    WD_FEED = WD_FEED_FEED2;
  }
}
