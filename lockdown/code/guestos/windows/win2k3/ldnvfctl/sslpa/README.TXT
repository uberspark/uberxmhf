integrating ssldump into the lockdown verifier control application
author: amit vasudevan (amitvasudevan@acm.org)

source files:

#
#    FILE DEPENDENCIES
#
#    file dependencies state, for each file that is built,
#    which file(s) it depends upon
#

$(OBJ_DIR)\debug.obj: $(COMMON_LIB_SRCDIR)\debug.h
$(OBJ_DIR)\debug.obj: $(COMMON_LIB_SRCDIR)\debug.c
	$(CC) $(CFLAGS) /Fo$@ $(COMMON_LIB_SRCDIR)\debug.c

$(OBJ_DIR)\r_assoc.obj: $(COMMON_LIB_SRCDIR)\r_assoc.c
	$(CC) $(CFLAGS) /Fo$@ $(COMMON_LIB_SRCDIR)\r_assoc.c

$(OBJ_DIR)\r_data.obj: $(COMMON_LIB_SRCDIR)\r_data.h
$(OBJ_DIR)\r_data.obj: $(COMMON_LIB_SRCDIR)\r_data.c
	$(CC) $(CFLAGS) /Fo$@ $(COMMON_LIB_SRCDIR)\r_data.c

$(OBJ_DIR)\r_errors.obj: $(COMMON_LIB_SRCDIR)\r_errors.c
	$(CC) $(CFLAGS) /Fo$@ $(COMMON_LIB_SRCDIR)\r_errors.c

$(OBJ_DIR)\r_list.obj: $(COMMON_LIB_SRCDIR)\r_list.c
	$(CC) $(CFLAGS) /Fo$@ $(COMMON_LIB_SRCDIR)\r_list.c

$(OBJ_DIR)\r_replace.obj: $(COMMON_LIB_SRCDIR)\r_replace.c
	$(CC) $(CFLAGS) /Fo$@ $(COMMON_LIB_SRCDIR)\r_replace.c

$(OBJ_DIR)\r_time.obj: $(COMMON_LIB_SRCDIR)\r_time.c
	$(CC) $(CFLAGS) /Fo$@ $(COMMON_LIB_SRCDIR)\r_time.c




$(OBJ_DIR)\network.obj: $(ANALYZE_SRCDIR)\network.h
$(OBJ_DIR)\network.obj: $(ANALYZE_SRCDIR)\network.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SRCDIR)\network.c

$(OBJ_DIR)\pcap-snoop.obj: $(ANALYZE_SRCDIR)\pcap-snoop.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SRCDIR)\pcap-snoop.c

$(OBJ_DIR)\proto_mod.obj: $(ANALYZE_SRCDIR)\proto_mod.h
$(OBJ_DIR)\proto_mod.obj: $(ANALYZE_SRCDIR)\proto_mod.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SRCDIR)\proto_mod.c

$(OBJ_DIR)\tcpconn.obj: $(ANALYZE_SRCDIR)\tcpconn.h
$(OBJ_DIR)\tcpconn.obj: $(ANALYZE_SRCDIR)\tcpconn.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SRCDIR)\tcpconn.c

$(OBJ_DIR)\tcppack.obj: $(ANALYZE_SRCDIR)\tcppack.h
$(OBJ_DIR)\tcppack.obj: $(ANALYZE_SRCDIR)\tcppack.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SRCDIR)\tcppack.c


$(OBJ_DIR)\null_analyze.obj: $(ANALYZE_NULL_SRCDIR)\null_analyze.h
$(OBJ_DIR)\null_analyze.obj: $(ANALYZE_NULL_SRCDIR)\null_analyze.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_NULL_SRCDIR)\null_analyze.c



$(OBJ_DIR)\ciphersuites.obj: $(ANALYZE_SSL_SRCDIR)\ciphersuites.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SSL_SRCDIR)\ciphersuites.c

$(OBJ_DIR)\ssl.enums.obj: $(ANALYZE_SSL_SRCDIR)\ssl.enums.h
$(OBJ_DIR)\ssl.enums.obj: $(ANALYZE_SSL_SRCDIR)\ssl.enums.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SSL_SRCDIR)\ssl.enums.c

$(OBJ_DIR)\ssl_analyze.obj: $(ANALYZE_SSL_SRCDIR)\ssl_analyze.h
$(OBJ_DIR)\ssl_analyze.obj: $(ANALYZE_SSL_SRCDIR)\ssl_analyze.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SSL_SRCDIR)\ssl_analyze.c

$(OBJ_DIR)\ssl_rec.obj: $(ANALYZE_SSL_SRCDIR)\ssl_rec.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SSL_SRCDIR)\ssl_rec.c

$(OBJ_DIR)\ssldecode.obj: $(ANALYZE_SSL_SRCDIR)\ssldecode.h
$(OBJ_DIR)\ssldecode.obj: $(ANALYZE_SSL_SRCDIR)\ssldecode.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SSL_SRCDIR)\ssldecode.c

$(OBJ_DIR)\sslprint.obj: $(ANALYZE_SSL_SRCDIR)\sslprint.h
$(OBJ_DIR)\sslprint.obj: $(ANALYZE_SSL_SRCDIR)\sslprint.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SSL_SRCDIR)\sslprint.c

$(OBJ_DIR)\sslxprint.obj: $(ANALYZE_SSL_SRCDIR)\sslxprint.h
$(OBJ_DIR)\sslxprint.obj: $(ANALYZE_SSL_SRCDIR)\sslxprint.c
	$(CC) $(CFLAGS) /Fo$@ $(ANALYZE_SSL_SRCDIR)\sslxprint.c

# global variables
SSLPA_ROOT=.
WINPCAP_DEV_DIR=$(SSLPA_ROOT)\win32\WPdpack
WINPCAP_SRC_DIR=$(SSLPA_ROOT)\win32\winpcap
WINPCAP_LIB_DIR=$(SSLPA_ROOT)\win32\wpcaplibs\WpdPack


# include dependencies
SSLPA_INCLUDES = -I$(SSLPA_ROOT)\base	\
	-I$(SSLPA_ROOT)\common\include	\
	-I$(SSLPA_ROOT)\common\lib	\
	-I$(SSLPA_ROOT)\null	\
	-I$(SSLPA_ROOT)\ssl	\
	-I$(SSLPA_ROOT)\win32	\  
	-I$(WINPCAP_DEV_DIR)\include	\ 
	-I$(WINPCAP_DEV_DIR)\include\net	\ 
	-I$(WINPCAP_SRC_DIR)\wpcap\libpcap\win32\include	\

# lib dependencies
SSLPA_LIBS = gdi32.lib	\ 
	Wsock32.lib	\ 
	kernel32.lib	\
	$(WINPCAP_LIB_DIR)\lib\wpcap.lib	\

# defines needed
SSLPA_DEFINES=/D STDC /D WIN32 /D _CONSOLE \
	$(OPENSSL_DEFINES) /D STDC_HEADERS /D SIZEOF_UNSIGNED_SHORT=2 /D SIZEOF_UNSIGNED_LONG=4 \
	/D RETSIGTYPE=void /D SIZEOF_CHAR=1 /D SIZEOF_SHORT=2 /D SIZEOF_INT=4

# cflags needed
SSLPA_CFLAGS = /MT /nologo /W3 $(SSLPA_INCLUDES) $(SSLPA_DEFINES) /FD /c 


# COMMON_LFLAGS=/nologo /subsystem:console /machine:I386 /opt:ref /incremental:no
