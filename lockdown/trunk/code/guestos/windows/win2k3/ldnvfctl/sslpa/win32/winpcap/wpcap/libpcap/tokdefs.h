typedef union {
	int i;
	bpf_u_int32 h;
	u_char *e;
	char *s;
	struct stmt *stmt;
	struct arth *a;
	struct {
		struct qual q;
		struct block *b;
	} blk;
	struct block *rblk;
} YYSTYPE;
#define	DST	257
#define	SRC	258
#define	HOST	259
#define	GATEWAY	260
#define	NET	261
#define	MASK	262
#define	PORT	263
#define	LESS	264
#define	GREATER	265
#define	PROTO	266
#define	PROTOCHAIN	267
#define	CBYTE	268
#define	ARP	269
#define	RARP	270
#define	IP	271
#define	TCP	272
#define	UDP	273
#define	ICMP	274
#define	IGMP	275
#define	IGRP	276
#define	PIM	277
#define	ATALK	278
#define	AARP	279
#define	DECNET	280
#define	LAT	281
#define	SCA	282
#define	MOPRC	283
#define	MOPDL	284
#define	TK_BROADCAST	285
#define	TK_MULTICAST	286
#define	NUM	287
#define	INBOUND	288
#define	OUTBOUND	289
#define	LINK	290
#define	GEQ	291
#define	LEQ	292
#define	NEQ	293
#define	ID	294
#define	EID	295
#define	HID	296
#define	HID6	297
#define	LSH	298
#define	RSH	299
#define	LEN	300
#define	IPV6	301
#define	ICMPV6	302
#define	AH	303
#define	ESP	304
#define	VLAN	305
#define	ISO	306
#define	ESIS	307
#define	ISIS	308
#define	CLNP	309
#define	OR	310
#define	AND	311
#define	UMINUS	312


extern YYSTYPE pcap_lval;
