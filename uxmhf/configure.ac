AC_INIT([uxmhf], [6.1.0])

###### simple configuration of tools. (just looks for matching binary on PATH)
AC_CHECK_PROG([MAKE], [make], [make])
AC_CHECK_PROG([UBERSPARKCONFIG], [ubersparkconfig], [ubersparkconfig])
AC_CHECK_PROG([FRAMAC], [frama-c], [frama-c])
AC_CHECK_PROG([CCERT], [ccomp], [ccomp])
AC_CHECK_PROG([CC], [gcc -m32], [gcc -m32])
AC_CHECK_PROG([AS], [as], [as])
AC_CHECK_PROG([AR], [ar], [ar])
AC_CHECK_PROG([RM], [rm -f], [rm -f])
AC_CHECK_PROG([CP], [cp], [cp])
AC_CHECK_PROG([MKDIR], [mkdir], [mkdir])
AC_CHECK_PROG([LD], [ld], [ld])
AC_CHECK_PROG([OBJCOPY], [objcopy], [objcopy])
AC_CHECK_PROG([CAT], [cat], [cat])

###### autoconf general options
AC_SUBST([prefix])

###### uxmhf specific options

# target cpu
AC_SUBST([TARGET_CPU])
AC_ARG_WITH([target_cpu],
        AS_HELP_STRING([--with-target-cpu=@<:@CPU@:>@],
                [select target cpu (x86)]),
                , [with_target_cpu=x86])
TARGET_CPU=$[]with_target_cpu

# target container
AC_SUBST([TARGET_CONTAINER])
AC_ARG_WITH([target_container],
        AS_HELP_STRING([--with-target-container=@<:@CONTAINER@:>@],
                [select target container (vmx)]),
                , [with_target_container=vmx])
TARGET_CONTAINER=$[]with_target_container

# target platform
AC_SUBST([TARGET_PLATFORM])
AC_ARG_WITH([target_platform],
        AS_HELP_STRING([--with-target-platform=@<:@PLATFORM@:>@],
                [select target platform (x86pc)]),
                , [with_target_platform=x86pc])
TARGET_PLATFORM=$[]with_target_platform


#debugging
AC_SUBST([DEBUG_SERIAL])
AC_SUBST([DEBUG_SERIAL_PORT])
AC_ARG_ENABLE([debug_serial],
        AS_HELP_STRING([--enable-debug-serial@<:@=PORT|no@:>@],
                [enable serial debugging on specified port]),
                , [enable_debug_serial=0x3f8])
AS_IF([test "x${enable_debug_serial}" != "xno"],
      [DEBUG_SERIAL=y
       DEBUG_SERIAL_PORT=$[]enable_debug_serial],
      [DEBUG_SERIAL=n])

#debugging
AC_SUBST([DEBUG_SERIAL_MAXCPUS])
AC_ARG_WITH([debug_serial_maxcpus],
        AS_HELP_STRING([--with-debug-serial-maxcpus@<:@=CPUS@:>@],
                [specify number of CPUS on the platform when debug mode is enabled]),
                , [with_debug_serial_maxcpus=8])
DEBUG_SERIAL_MAXCPUS=$[]with_debug_serial_maxcpus



# selectively enable/disable Dynamic Root-of-Trust (DRT)
AC_SUBST([DRT])
AC_ARG_ENABLE([drt],
        AS_HELP_STRING([--enable-drt@<:@=yes|no@:>@],
                [enable Dynamic Root-of-Trust (DRT)]),
                , [enable_drt=yes])
AS_IF([test "x${enable_drt}" != "xno"],
      [DRT=y],
      [DRT=n])


# selectively enable/disable DMA protection (DMAP)
AC_SUBST([DMAP])
AC_ARG_ENABLE([dmap],
        AS_HELP_STRING([--enable-dmap@<:@=yes|no@:>@],
                [enable DMA protection]),
                , [enable_dmap=yes])
AS_IF([test "x${enable_dmap}" != "xno"],
      [DMAP=y],
      [DMAP=n])


###### autoconf output files
AC_CONFIG_FILES(
			[uxmhf-common.mk]
			[Makefile]
			[xmhf-uobjs/UOBJLIST]
	)

AC_OUTPUT
