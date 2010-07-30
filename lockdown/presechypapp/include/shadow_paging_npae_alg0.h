//shadow_paging.h 
//definitions for shadow paging (non-PAE)
//algorithm 0
//author: amit vasudevan (amitvasudevan@acm.org)
#ifndef _SHADOW_PAGING_NPAE_ALG0_H_
#define _SHADOW_PAGING_NPAE_ALG0_H_

extern u32 __shadow_alg0_area[];
extern u32 shadow_guest_CR3;

u32 shadow_page_fault(u32 cr2, u32 error_code);
void shadow_invalidate_page(u32 address);
u32 shadow_new_context(u32 guest_CR3);

#define	ENOMEM	12

#define IS_ERR(x) ((unsigned long)x == (unsigned long)-ENOMEM)
#define __va(x) ((u32)x)
#define __pa(x) ((u32)x)

static inline void *ERR_PTR(long error)
{
        return (void *) error;
}

/* PAGE_SHIFT determines the page size */
#define PAGE_SHIFT      12
#define PAGE_SIZE       (0x1UL << PAGE_SHIFT)
#define PAGE_MASK       (~(PAGE_SIZE-1))


/*
* Simple doubly linked list implementation.
*
* Some of the internal functions ("__xxx") are useful when
* manipulating whole lists rather than single entries, as
* sometimes we already know the next/prev entries and we can
* generate better code by using them directly rather than
* using the generic single-entry routines.
*/

struct list_head {
       struct list_head *next, *prev;
};

#define LIST_HEAD_INIT(name) { &(name), &(name) }

#define LIST_HEAD(name) \
     struct list_head name = LIST_HEAD_INIT(name)

static inline void INIT_LIST_HEAD(struct list_head *list)
{
        list->next = list;
        list->prev = list;
}

enum km_type {
  KM_BOUNCE_READ,
  KM_SKB_SUNRPC_DATA,
  KM_SKB_DATA_SOFTIRQ,
  KM_USER0,
  KM_USER1,
  KM_BIO_SRC_IRQ,
  KM_BIO_DST_IRQ,
  KM_PTE0,
  KM_PTE1,
  KM_IRQ0,
  KM_IRQ1,
  KM_SOFTIRQ0,
  KM_SOFTIRQ1,
  KM_SYNC_ICACHE,
  KM_SYNC_DCACHE,
  KM_UML_USERCOPY,
  KM_IRQ_PTE,
  KM_NMI,
  KM_NMI_PTE,
  KM_TYPE_NR
};

#define pfn_to_page(x) ((x) << PAGE_SHIFT)
#define kmap_atomic(x, y) ((u32)x)
#define kunmap_atomic(x, y) 

#define LIST_POISON1  ((void *) 0x00100100)
#define LIST_POISON2  ((void *) 0x00200200)

/*
* Delete a list entry by making the prev/next entries
* point to each other.
*
* This is only for internal list manipulation where we know
* the prev/next entries already!
*/
static inline void __list_del(struct list_head * prev, struct list_head * next)
{
        next->prev = prev;
        prev->next = next;
}

static inline void list_del(struct list_head *entry)
{
        __list_del(entry->prev, entry->next);
        entry->next = LIST_POISON1;
        entry->prev = LIST_POISON2;
}

/*
 * Insert a new entry between two known consecutive entries.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline void __list_add(struct list_head *new,
                              struct list_head *prev,
                              struct list_head *next)
{
        next->prev = new;
        new->next = next;
        new->prev = prev;
        prev->next = new;
}

/**
 * list_add - add a new entry
 * @new: new entry to be added
 * @head: list head to add it after
 *
 * Insert a new entry after the specified head.
 * This is good for implementing stacks.
 */
static inline void list_add(struct list_head *new, struct list_head *head)
{
        __list_add(new, head, head->next);
}


#define offsetof(TYPE, MEMBER) ((unsigned long) &((TYPE *)0)->MEMBER)

#define container_of(ptr, type, member) ({                      \
        typeof( ((type *)0)->member ) *__mptr = (ptr);    \
        (type *)( (char *)__mptr - offsetof(type,member) );})


/**
 * list_entry - get the struct for this entry
 * @ptr:        the &struct list_head pointer.
 * @type:       the type of the struct this is embedded in.
 * @member:     the name of the list_struct within the struct.
*/
#define list_entry(ptr, type, member) \
        container_of(ptr, type, member)


/**
 * list_empty - tests whether a list is empty
 * @head: the list to test.
 */
static inline int list_empty(const struct list_head *head)
{
        return head->next == head;
}


/**
 * list_for_each_entry_safe - iterate over list of given type safe against removal of list entry
 * @pos:        the type * to use as a loop cursor.
 * @n:          another type * to use as temporary storage
 * @head:       the head for your list.
 * @member:     the name of the list_struct within the struct.
 */
#define list_for_each_entry_safe(pos, n, head, member)                  \
        for (pos = list_entry((head)->next, typeof(*pos), member),      \
                n = list_entry(pos->member.next, typeof(*pos), member); \
             &pos->member != (head);                                    \
             pos = n, n = list_entry(n->member.next, typeof(*n), member))





//------------------------------------------------------------------------------

/*
 * Address types:
 *
 *  gva - guest virtual address
 *  gpa - guest physical address
 *  gfn - guest frame number
 *  hva - host virtual address
 *  hpa - host physical address
 *  hfn - host frame number
 */

typedef unsigned long  gva_t;
typedef u64            gpa_t;
typedef unsigned long  gfn_t;

typedef unsigned long  hva_t;
typedef u64            hpa_t;
typedef unsigned long  hfn_t;

#define gpa_to_hpa(x, y) ((u32)y)

#define INVALID_PAGE (~(hpa_t)0)
#define UNMAPPED_GVA (~(gpa_t)0)

#define KVM_MAX_VCPUS 1
#define KVM_MEMORY_SLOTS 4
#define KVM_NUM_MMU_PAGES 256

#define CR3_FLAGS_MASK ((1ULL << 5) - 1)

#define PT64_ENT_PER_PAGE 512
#define PT32_ENT_PER_PAGE 1024

#define PT_WRITABLE_SHIFT 1

#define PT_PRESENT_MASK (1ULL << 0)
#define PT_WRITABLE_MASK (1ULL << PT_WRITABLE_SHIFT)
#define PT_USER_MASK (1ULL << 2)
#define PT_PWT_MASK (1ULL << 3)
#define PT_PCD_MASK (1ULL << 4)
#define PT_ACCESSED_MASK (1ULL << 5)
#define PT_DIRTY_MASK (1ULL << 6)
#define PT_PAGE_SIZE_MASK (1ULL << 7)
#define PT_PAT_MASK (1ULL << 7)
#define PT_GLOBAL_MASK (1ULL << 8)
#define PT64_NX_MASK (1ULL << 63)

#define PT_PAT_SHIFT 7
#define PT_DIR_PAT_SHIFT 12
#define PT_DIR_PAT_MASK (1ULL << PT_DIR_PAT_SHIFT)

#define PT32_DIR_PSE36_SIZE 4
#define PT32_DIR_PSE36_SHIFT 13
#define PT32_DIR_PSE36_MASK (((1ULL << PT32_DIR_PSE36_SIZE) - 1) << PT32_DIR_PSE36_SHIFT)


#define PT32_PTE_COPY_MASK \
	(PT_PRESENT_MASK | PT_ACCESSED_MASK | PT_DIRTY_MASK | PT_GLOBAL_MASK)

#define PT64_PTE_COPY_MASK (PT64_NX_MASK | PT32_PTE_COPY_MASK)

#define PT_FIRST_AVAIL_BITS_SHIFT 9
#define PT64_SECOND_AVAIL_BITS_SHIFT 52

#define PT_SHADOW_PS_MARK (1ULL << PT_FIRST_AVAIL_BITS_SHIFT)
#define PT_SHADOW_IO_MARK (1ULL << PT_FIRST_AVAIL_BITS_SHIFT)

#define PT_SHADOW_WRITABLE_SHIFT (PT_FIRST_AVAIL_BITS_SHIFT + 1)
#define PT_SHADOW_WRITABLE_MASK (1ULL << PT_SHADOW_WRITABLE_SHIFT)

#define PT_SHADOW_USER_SHIFT (PT_SHADOW_WRITABLE_SHIFT + 1)
#define PT_SHADOW_USER_MASK (1ULL << (PT_SHADOW_USER_SHIFT))

#define PT_SHADOW_BITS_OFFSET (PT_SHADOW_WRITABLE_SHIFT - PT_WRITABLE_SHIFT)

#define VALID_PAGE(x) ((x) != INVALID_PAGE)

#define PT64_LEVEL_BITS 9

#define PT64_LEVEL_SHIFT(level) \
		( PAGE_SHIFT + (level - 1) * PT64_LEVEL_BITS )

#define PT64_LEVEL_MASK(level) \
		(((1ULL << PT64_LEVEL_BITS) - 1) << PT64_LEVEL_SHIFT(level))

#define PT64_INDEX(address, level)\
	(((address) >> PT64_LEVEL_SHIFT(level)) & ((1 << PT64_LEVEL_BITS) - 1))


#define PT32_LEVEL_BITS 10

#define PT32_LEVEL_SHIFT(level) \
		( PAGE_SHIFT + (level - 1) * PT32_LEVEL_BITS )

#define PT32_LEVEL_MASK(level) \
		(((1ULL << PT32_LEVEL_BITS) - 1) << PT32_LEVEL_SHIFT(level))

#define PT32_INDEX(address, level)\
	(((address) >> PT32_LEVEL_SHIFT(level)) & ((1 << PT32_LEVEL_BITS) - 1))


#define PT64_BASE_ADDR_MASK (((1ULL << 52) - 1) & PAGE_MASK)
#define PT64_DIR_BASE_ADDR_MASK \
	(PT64_BASE_ADDR_MASK & ~((1ULL << (PAGE_SHIFT + PT64_LEVEL_BITS)) - 1))

#define PT32_BASE_ADDR_MASK PAGE_MASK
#define PT32_DIR_BASE_ADDR_MASK \
	(PAGE_MASK & ~((1ULL << (PAGE_SHIFT + PT32_LEVEL_BITS)) - 1))


#define PFERR_PRESENT_MASK (1U << 0)
#define PFERR_WRITE_MASK (1U << 1)
#define PFERR_USER_MASK (1U << 2)

#define PT64_ROOT_LEVEL 4
#define PT32_ROOT_LEVEL 2
#define PT32E_ROOT_LEVEL 3

#define PT_DIRECTORY_LEVEL 2
#define PT_PAGE_TABLE_LEVEL 1

#define PTTYPE 32	//NPAE paging

#if PTTYPE == 64
	#define pt_element_t u64
	#define guest_walker guest_walker64
	#define FNAME(name) paging##64_##name
	#define PT_BASE_ADDR_MASK PT64_BASE_ADDR_MASK
	#define PT_DIR_BASE_ADDR_MASK PT64_DIR_BASE_ADDR_MASK
	#define PT_INDEX(addr, level) PT64_INDEX(addr, level)
	#define SHADOW_PT_INDEX(addr, level) PT64_INDEX(addr, level)
	#define PT_LEVEL_MASK(level) PT64_LEVEL_MASK(level)
	#define PT_PTE_COPY_MASK PT64_PTE_COPY_MASK
#elif PTTYPE == 32
	#define pt_element_t u32
	#define guest_walker guest_walker32
	#define FNAME(name) paging##32_##name
	#define PT_BASE_ADDR_MASK PT32_BASE_ADDR_MASK
	#define PT_DIR_BASE_ADDR_MASK PT32_DIR_BASE_ADDR_MASK
	#define PT_INDEX(addr, level) PT32_INDEX(addr, level)
	#define SHADOW_PT_INDEX(addr, level) PT64_INDEX(addr, level)
	#define PT_LEVEL_MASK(level) PT32_LEVEL_MASK(level)
	#define PT_PTE_COPY_MASK PT32_PTE_COPY_MASK
#else
	#error Invalid PTTYPE value
#endif

/*
 * The guest_walker structure emulates the behavior of the hardware page
 * table walker.
 */
struct guest_walker {
	int level;
	pt_element_t *table;
	pt_element_t inherited_ar;
};


struct kvm_mmu_page {
	struct list_head link;
	hpa_t page_hpa;
	//unsigned long slot_bitmap; /* One bit set per slot which has memory
	//			    * in this shadow page.
	//			    */
	int global;              /* Set if all ptes in this page are global */
	u64 *parent_pte;
};


struct kvm_vcpu;

struct kvm {
	//spinlock_t lock; /* protects everything except vcpus */
	//int nmemslots;
	//struct kvm_memory_slot memslots[KVM_MEMORY_SLOTS];
	struct list_head active_mmu_pages;
	//struct kvm_vcpu vcpus[KVM_MAX_VCPUS];
	//int memory_config_version;
	//int busy;
};

/*
 * x86 supports 3 paging modes (4-level 64-bit, 3-level 64-bit, and 2-level
 * 32-bit).  The kvm_mmu structure abstracts the details of the current mmu
 * mode.
 */
struct kvm_mmu {
	void (*new_cr3)(struct kvm_vcpu *vcpu);
	int (*page_fault)(struct kvm_vcpu *vcpu, gva_t gva, u32 err);
	void (*inval_page)(struct kvm_vcpu *vcpu, gva_t gva);
	//void (*free)(struct kvm_vcpu *vcpu);
	//gpa_t (*gva_to_gpa)(struct kvm_vcpu *vcpu, gva_t gva);
	hpa_t root_hpa;
	int root_level;
	int shadow_root_level;
};


struct kvm_vcpu {
	struct kvm *kvm;
	//union {
	//	struct vmcs *vmcs;
	//	struct vcpu_svm *svm;
	//};
	//struct mutex mutex;
	//int   cpu;
	//int   launched;
	//int interrupt_window_open;
	//unsigned long irq_summary; /* bit vector: 1 per word in irq_pending */
//#define NR_IRQ_WORDS KVM_IRQ_BITMAP_SIZE(unsigned long)
	//unsigned long irq_pending[NR_IRQ_WORDS];
	//unsigned long regs[NR_VCPU_REGS]; /* for rsp: vcpu_load_rsp_rip() */
	//unsigned long rip;      /* needs vcpu_load_rsp_rip() */

	unsigned long cr0;
	unsigned long cr2;
	unsigned long cr3;
	unsigned long cr4;
	//unsigned long cr8;
	//u64 shadow_efer;
	//u64 apic_base;
	//int nmsrs;
	//struct vmx_msr_entry *guest_msrs;
	//struct vmx_msr_entry *host_msrs;

	struct list_head free_pages;
	struct kvm_mmu_page page_header_buf[KVM_NUM_MMU_PAGES];
	unsigned long page_private[KVM_NUM_MMU_PAGES]; //added
	struct kvm_mmu mmu;

	//struct kvm_guest_debug guest_debug;

	//char fx_buf[FX_BUF_SIZE];
	//char *host_fx_image;
	//char *guest_fx_image;

	//int mmio_needed;
	//int mmio_read_completed;
	//int mmio_is_write;
	//int mmio_size;
	//unsigned char mmio_data[8];
	//gpa_t mmio_phys_addr;

	//struct {
	//	int active;
	//	u8 save_iopl;
	//	struct kvm_save_segment {
	//		u16 selector;
	//		unsigned long base;
	//		u32 limit;
	//		u32 ar;
	//	} tr, es, ds, fs, gs;
	//} rmode;
};

static inline struct kvm_mmu_page *page_header(struct kvm_vcpu *vcpu, hpa_t shadow_page)
{
	u32 index = (u32)shadow_page - (u32)__shadow_alg0_area;
	return (struct kvm_mmu_page *)vcpu->page_private[index];
	//struct page *page = (struct page *)pfn_to_page(shadow_page >> PAGE_SHIFT);

	//return (struct kvm_mmu_page *)page->private;
	
	
	//return ( (struct kvm_mmu_page *)(u32)pfn_to_page(shadow_page >> PAGE_SHIFT) );
}

static inline int is_long_mode(struct kvm_vcpu *vcpu)
{
#ifdef CONFIG_X86_64
	return vcpu->shadow_efer & EFER_LME;
#else
	return 0;
#endif
}

static inline int is_pae(struct kvm_vcpu *vcpu)
{
	return vcpu->cr4 & CR4_PAE;
}

static inline int is_pse(struct kvm_vcpu *vcpu)
{
	return vcpu->cr4 & CR4_PSE;
}

static inline int is_paging(struct kvm_vcpu *vcpu)
{
	return vcpu->cr0 & CR0_PG;
}


#endif // __SHADOW_PAGING_NPAE_ALG0_H_
