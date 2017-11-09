AC_INIT([uxmhf-rpi3], [1.0])


###### autoconf general options
AC_SUBST([prefix])

###### uxmhf-rpi3 specific options

# core start address
AC_SUBST([CORE_STARTADDR])
AC_ARG_WITH([core_startaddr],
        AS_HELP_STRING([--with-core-startaddr=@<:@STARTADDR@:>@],
                [select core_startaddr (0x1000000)]),
                , [with_core_startaddr=0x1000000])
CORE_STARTADDR=$[]with_core_startaddr

# core size
AC_SUBST([CORE_SIZE])
AC_ARG_WITH([core_size],
        AS_HELP_STRING([--with-core-size=@<:@SIZE@:>@],
                [select core_size (0xC00000)]),
                , [with_core_size=0xC00000])
CORE_SIZE=$[]with_core_size


###### autoconf output files
AC_CONFIG_FILES(
			[./include/config.h]
	)

AC_OUTPUT
