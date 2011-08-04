/* based on IEEE Std 1003.1-2008
 * http://pubs.opengroup.org/onlinepubs/9699919799/basedefs/termios.h.html
 */

#ifndef	_SYS_TERMIOS_H
# define _SYS_TERMIOS_H

typedef unsigned char cc_t;
typedef unsigned short tcflag_t;
typedef unsigned char speed_t;

# define NCCS 13

struct termios {
  tcflag_t	c_iflag;
  tcflag_t	c_oflag;
  tcflag_t	c_cflag;
  tcflag_t	c_lflag;
  cc_t		c_cc[NCCS];

  /* implementation-specific */
  speed_t         c_ispeed;
  speed_t         c_ospeed;
};

/* The <termios.h> header shall define the following symbolic
   constants for use as subscripts for the array c_cc: */
# define VEOF	4	/* also VMIN -- thanks, AT&T */
# define VEOL	5	/* also VTIME -- thanks again */
# define VERASE	2
# define VINTR	0
# define VKILL	3
# define VMIN	4	/* also VEOF */
# define VQUIT	1
# define VSUSP	10
# define VTIME	5	/* also VEOL */
# define VSTART	11
# define VSTOP	12

/* The <termios.h> header shall define the following symbolic
   constants for use as flags in the c_iflag field. The c_iflag field
   describes the basic terminal input control. */
# define IGNBRK	000001 /* Ignore break condition. */
# define BRKINT	000002 /* Signal interrupt on break */
# define IGNPAR	000004 /* Ignore characters with parity errors. */
# define INPCK	000020 /* Enable input parity check. */
# define ISTRIP	000040 /* Strip character. */
# define INLCR	000100 /* Map NL to CR on input. */
# define IGNCR	000200 /* Ignore CR. */
# define ICRNL	000400 /* Map CR to NL on input. */
# define IXON	002000 /* Enable start/stop output control. */
# define IXOFF	010000 /* Enable start/stop input control. */
# define IXANY  020000 /* Enable any character to restart output. */

/* The <termios.h> header shall define the following symbolic
   constants for use as flags in the c_oflag field. The c_oflag field
   specifies the system treatment of output. */
# define OPOST	000001 /* Post-process output. */
# define OCRNL	000004 /* Map CR to NL on output. */
# define ONLCR	000010 /* Map NL to CR-NL on output. */
# define ONOCR	000020 /* No CR output at column 0 */
# define ONLRET 000040 /* NL performs CR function. */
# define OFDEL  000080 /* Fill is DEL. */
# define OFILL  000100 /* Use fill characters for delay */
# define NLDLY  0000400
# define   NL0  0000000
# define   NL1  0000400
# define CRDLY  0003000
# define   CR0  0000000
# define   CR1  0001000
# define   CR2  0002000
# define   CR3  0003000
# define TABDLY 0014000
# define   TAB0 0000000
# define   TAB1 0004000
# define   TAB2 0010000
# define   TAB3 0014000
# define BSDLY  0020000
# define   BS0  0000000
# define   BS1  0020000
# define VTDLY   0040000
# define   VT0   0000000
# define   VT1   0040000
# define FFDLY  0100000
# define   FF0  0000000
# define   FF1  0100000

/* The <termios.h> header shall define the following symbolic
   constants for use as values of objects of type speed_t. */
/* The input and output baud rates are stored in the termios
   structure. These are the valid values for objects of type
   speed_t. Not all baud rates need be supported by the underlying
   hardware. */
# define B0	000000
# define B50	000001
# define B75	000002
# define B110	000003
# define B134	000004
# define B150	000005
# define B200	000006
# define B300	000007
# define B600	000010
# define B1200	000011
# define B1800	000012
# define B2400	000013
# define B4800	000014
# define B9600	000015
# define B19200	000016
# define B38400	000017

/* The <termios.h> header shall define the following symbolic
   constants for use as flags in the c_cflag field. The c_cflag field
   describes the hardware control of the terminal; not all values
   specified are required to be supported by the underlying
   hardware. */
# define CLOCAL	004000
# define CREAD	000200
# define CSIZE	000060
# define CS5	0
# define CS6	020
# define CS7	040
# define CS8	060
# define CSTOPB	000100
# define HUPCL	002000
# define PARENB	000400
# define PAODD	001000

/* The <termios.h> header shall define the following symbolic
   constants for use as flags in the c_lflag field. The c_lflag field
   of the argument structure is used to control various terminal
   functions. */
# define ECHO	0000010
# define ECHOE	0000020
# define ECHOK	0000040
# define ECHONL	0000100
# define ICANON	0000002
# define IEXTEN	0000400
# define ISIG	0000001
# define NOFLSH	0000200
# define TOSTOP	0001000

/* XXX implementation-specific */
# define _XCGETA (('x'<<8)|1)
# define _XCSETA (('x'<<8)|2)
# define _XCSETAW (('x'<<8)|3)
# define _XCSETAF (('x'<<8)|4)
# define _TCSBRK (('T'<<8)|5)
# define _TCFLSH (('T'<<8)|7)
# define _TCXONC (('T'<<8)|6)

/* The <termios.h> header shall define the following symbolic
   constants for use with tcsetattr(): */
# define TCSAFLUSH	_XCSETAF
# define TCSANOW	_XCSETA
# define TCSADRAIN	_XCSETAW
# define TCSADFLUSH	_XCSETAF /* non-standard */

/* The <termios.h> header shall define the following symbolic
   constants for use with tcflush(): */
# define TCIFLUSH	0
# define TCOFLUSH	1
# define TCIOFLUSH	2

/* The <termios.h> header shall define the following symbolic
   constants for use with tcflow(): */
# define TCOOFF	0
# define TCOON	1
# define TCIOFF	2
# define TCION	3

/* The <termios.h> header shall define the pid_t type as described in
   <sys/types.h>. */
/* XXX */

/* The following shall be declared as functions and may also be
   defined as macros. Function prototypes shall be provided. */
speed_t cfgetispeed(const struct termios *);
speed_t cfgetospeed(const struct termios *);
int     cfsetispeed(struct termios *, speed_t);
int     cfsetospeed(struct termios *, speed_t);
int     tcdrain(int);
int     tcflow(int, int);
int     tcflush(int, int);
int     tcgetattr(int, struct termios *);
/* pid_t   tcgetsid(int); XXX */
int     tcsendbreak(int, int);
int     tcsetattr(int, int, const struct termios *);

#endif	/* _SYS_TERMIOS_H */

