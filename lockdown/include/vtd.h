
void vtd_initialize(void);
void vtd_handlefault(void);
void vtd_setprotection(u32 spaddr, u32 epaddr, u32 type);

extern u32 vtd_iotlb_reg_off;

#define VTD_RSDP_SIGNATURE  (0x2052545020445352ULL) //"RSD PTR " 
#define VTD_DMAR_SIGNATURE  (0x52414D44) //"DMAR"
#define VTD_MAXDRHD   8   
#define VTD_MAXRMRR   8   
#define VTD_MAXATSR   8   
#define VTD_PROTECT 0
#define VTD_UNPROTECT 0

#define VTD_BIT_INTR_REMAP  0

#define VTD_INTR_REMAP  (1ULL << VTD_BIT_INTR_REMAP)

//ACPI RSDP structure
typedef struct {
  u64 signature;
  u8 checksum;
  u8 oemid[6];
  u8 revision;
  u32 rstdaddress;
  u32 length;
  u64 xsdtaddress;
  u8 xchecksum;
  u8 rsvd0[3];
} __attribute__ ((packed)) RSDP;

//ACPI XSDT structure
typedef struct {
	u32 signature;
	u32 length;
	u8 revision;
	u8 checksum;
	u8 oemid[6];
	u64 oemtableid;
	u32 oemrevision;
	u32 creatorid;
	u32 creatorrevision;
} __attribute__ ((packed)) XSDT;

//DMAR structure
typedef struct{
  u32 signature;
  u32 length;
  u8 revision;
  u8 checksum;
  u8 oemid[6];
  u64 oemtableid;
	u32 oemrevision;
	u32 creatorid;
	u32 creatorrevision;
  u8 hostaddresswidth;
  u8 flags;
  u8 rsvdz[10];    
}__attribute__ ((packed)) DMAR;

//DRHD structure
typedef struct{
  u16 type;
  u16 length;
  u8 flags;
  u8 rsvdz0;
  u16 pcisegment;
  u64 regbaseaddr;
}__attribute__ ((packed)) DRHD;

//RMRR structure
typedef struct{
  u16 type;
  u16 length;
  u16 rsvdz0;
  u16 pcisegment;
  u64 rmrrbaseaddress;
  u64 rmrrlimitaddress;
}__attribute__ ((packed)) RMRR;


//ATSR structure
typedef struct{
  u16 type;
  u16 length;
  u8 flags;
  u8 rsvdz0;
  u16 pcisegment;
}__attribute__ ((packed)) ATSR;

#define VTD_REG_32BITS  0
#define VTD_REG_64BITS  1
#define VTD_REG_128BITS 2
#define VTD_REG_READ  0
#define VTD_REG_WRITE 1

//vtd general registers
#define VTD_VER_REG_OFF 0x000
#define VTD_CAP_REG_OFF 0x008
#define VTD_ECAP_REG_OFF  0x010
#define VTD_GCMD_REG_OFF  0x018
#define VTD_GSTS_REG_OFF  0x01C
#define VTD_RTADDR_REG_OFF  0x020
#define VTD_PMEN_REG_OFF  0x064


//vtd registers for fault reporting
#define VTD_FECTL_REG_OFF 0x038
#define VTD_FSTS_REG_OFF  0x034

//vtd registers for cache invalidation
#define VTD_IVA_REG_OFF  0x0DEAD  //the offset of this register is computed
                                    //at runtime for a specified DMAR device
#define VTD_IOTLB_REG_OFF   0x0BEEF     //this is relative to VTD_IVA_REG_OFF + 8

#define VTD_CCMD_REG_OFF  0x028

//vtd register structures
typedef union {
  u32 value;
  struct
  {
    u32 min : 4;
    u32 max : 4;
    u32 rsvdz : 24;
  } bits;
} __attribute__ ((packed)) VTD_VER_REG;

typedef union {
  u64 value;
  struct
  {
    u32 nd : 3;
    u32 afl : 1;
    u32 rwbf : 1;
    u32 plmr : 1;
    u32 phmr : 1;
    u32 cm : 1;
    u32 sagaw: 5;
    u32 rsvdz0: 3;
    u32 mgaw : 6;
    u32 zlr: 1;
    u32 isoch: 1;
    u32 fro : 10;
    u32 sps : 4;
    u32 rsvdz1: 1;
    u32 psi: 1;
    u32 nfr: 8;
    u32 mamv: 6;
    u32 dwd: 1;
    u32 drd: 1;
    u32 rsvdz2: 8;
  } bits;
} __attribute__ ((packed)) VTD_CAP_REG;

typedef union {
  u64 value;
  struct
  {
    u32 c:1;
    u32 qi:1;
    u32 di:1;
    u32 ir:1;
    u32 eim:1;
    u32 ch:1;
    u32 pt:1; 
    u32 sc:1;
    u32 iro:10;
    u32 rsvdz0: 2;
    u32 mhmv: 4;
    u64 rsvdz1: 40;
  } bits;
} __attribute__ ((packed)) VTD_ECAP_REG;


typedef union {
  u32 value;
  struct
  {
    u32 rsvdz0: 23;
    u32 cfi: 1;
    u32 sirtp: 1;
    u32 ire:1;
    u32 qie:1;
    u32 wbf:1;
    u32 eafl:1;
    u32 sfl:1;
    u32 srtp:1;
    u32 te:1;
  } bits;
} __attribute__ ((packed)) VTD_GCMD_REG;

typedef union {
  u32 value;
  struct
  {
    u32 rsvdz0: 23;
    u32 cfis:1;
    u32 irtps:1;
    u32 ires:1;
    u32 qies:1;
    u32 wbfs:1;
    u32 afls:1;
    u32 fls:1;
    u32 rtps:1;
    u32 tes:1; 
  } bits;
} __attribute__ ((packed)) VTD_GSTS_REG;

typedef union {
  u64 value;
  struct
  {
    u32 rsvdz0: 12;
    u64 rta: 52;
  } bits;
} __attribute__ ((packed)) VTD_RTADDR_REG;

typedef union {
  u64 value;
  struct
  {
    u32 rsvdz0: 32;
    u32 did:16;
    u32 dw: 1;
    u32 dr:1;
    u32 rsvdz1: 7;
    u32 iaig: 3;
    u32 iirg: 3;
    u32 ivt: 1; 
  } bits;
} __attribute__ ((packed)) VTD_IOTLB_REG;

typedef union {
  u64 value;
  struct
  {
    u32 am: 6;
    u32 ih:1;
    u32 rsvdz0: 5;
    u64 addr:52;
  } bits;
} __attribute__ ((packed)) VTD_IVA_REG;

typedef union {
  u64 value;
  struct
  {
    u32 did:16;
    u32 sid:16;
    u32 fm:2;
    u32 rsvdz0: 25;
    u32 caig:2;
    u32 cirg:2;
    u32 icc:1; 
  } bits;
} __attribute__ ((packed)) VTD_CCMD_REG;


typedef union {
  u32 value;
  struct
  {
    u32 rsvdp0:30;
    u32 ip:1;
    u32 im:1;
  } bits;
} __attribute__ ((packed)) VTD_FECTL_REG;

typedef union {
  u32 value;
  struct
  {
    u32 pfo:1;
    u32 ppf:1;
    u32 afo:1;
    u32 apf:1;
    u32 iqe:1;
    u32 ice:1;
    u32 ite:1;
    u32 rsvdz0: 1;
    u32 fri:8;
    u32 rsvdz1: 16;
  } bits;
} __attribute__ ((packed)) VTD_FSTS_REG;

typedef union {
  u32 value;
  struct
  {
    u32 prs:1;
    u32 rsvdp:30;
    u32 epm:1;
  } bits;
} __attribute__ ((packed)) VTD_PMEN_REG;
