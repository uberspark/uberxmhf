# top-level Makefile for tools
# author: amit vasudevan (amitvasudevan@acm.org)

.PHONY: all
all: umf ubp

.PHONY: umf
umf:
	$(RM) -f umfcommon.annot
	$(RM) -f umfcommon.cmi
	$(RM) -f umfcommon.cmo
	$(RM) -f umfcommon.cmt
	$(RM) -f umfcommon.cmx
	$(RM) -f umfcommon.o
	$(MAKE) -f umf.mk -w all

	
.PHONY: ubp
ubp:
	$(RM) -f umfcommon.annot
	$(RM) -f umfcommon.cmi
	$(RM) -f umfcommon.cmo
	$(RM) -f umfcommon.cmt
	$(RM) -f umfcommon.cmx
	$(RM) -f umfcommon.o
	$(MAKE) -f ubp.mk -w all
	