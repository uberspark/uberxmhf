//------------------------------------------------------------------------------
// shadow_paging_npae.c
//
// intel vt-x hypervisor memory isolation using shadow paging (non-PAE mode)
// algorithm 0
// author: amit vasudevan (amitvasudevan@acm.org)

#include <types.h>
#include <target.h>
#include <print.h>
#include <processor.h>
#include <msr.h>
#include <vtx.h>
#include <paging.h>
#include <io.h>
#include <str.h>
#include <machine.h>
#include <error.h>
#include <shadow_paging_npae_alg0.h>

u32 shadow_guest_CR3=0;

struct kvm_vcpu vcpu;
struct kvm kvm;

/*
	A note of all events that cause TLB flushes on the IA-32
	
	1. Writing to a MTRR with WRMSR -> ALL TLB 
	2. Writing to CR0 to modify PG or PE flags -> ALL TLB
	3. Writing to CR4 to modify PSE, PGE or PAE flags -> ALL TLB
	4. INVLPG ->  TLB of address including global
	5. MOV to CR3 -> ALL TLB except global
	6. Task Switch changing value of CR3 -> ALL TLB except global
	7. VMX transitions -> ALL TLB 
*/

static int is_write_protection(struct kvm_vcpu *vcpu)
{
	return vcpu->cr0 & CR0_WP;
}

static int is_cpuid_PSE36(void)
{
	return 1;
}

static int is_present_pte(unsigned long pte)
{
	return pte & PT_PRESENT_MASK;
}

static int is_writeble_pte(unsigned long pte)
{
	return pte & PT_WRITABLE_MASK;
}

static int is_io_pte(unsigned long pte)
{
	return pte & PT_SHADOW_IO_MARK;
}

static void kvm_mmu_free_page(struct kvm_vcpu *vcpu, hpa_t page_hpa)
{
	struct kvm_mmu_page *page_head = page_header(vcpu, page_hpa);

	list_del(&page_head->link);
	page_head->page_hpa = page_hpa;
	list_add(&page_head->link, &vcpu->free_pages);
}

static int is_empty_shadow_page(hpa_t page_hpa)
{
	u32 *pos;
	u32 *end;
	for (pos = (u32 *)__va(page_hpa), end = pos + PAGE_SIZE / sizeof(u32);
		      pos != end; pos++)
		if (*pos != 0)
			return 0;
	return 1;
}

static hpa_t kvm_mmu_alloc_page(struct kvm_vcpu *vcpu, u64 *parent_pte)
{
	struct kvm_mmu_page *page;

	if (list_empty(&vcpu->free_pages))
		return INVALID_PAGE;

	page = list_entry(vcpu->free_pages.next, struct kvm_mmu_page, link);
	list_del(&page->link);
	list_add(&page->link, &vcpu->kvm->active_mmu_pages);
	ASSERT(is_empty_shadow_page(page->page_hpa));
	//page->slot_bitmap = 0;
	page->global = 1;
	page->parent_pte = parent_pte;
	return page->page_hpa;
}

hpa_t safe_gpa_to_hpa(struct kvm_vcpu *vcpu, gpa_t gpa)
{
	//hpa_t hpa = gpa_to_hpa(vcpu, gpa);

	//return is_error_hpa(hpa) ? bad_page_address | (gpa & ~PAGE_MASK): hpa;
	return (hpa_t)(u32)gpa;
}

static void release_pt_page_64(struct kvm_vcpu *vcpu, hpa_t page_hpa,
			       int level)
{
	ASSERT(vcpu);
	ASSERT(VALID_PAGE(page_hpa));
	ASSERT(level <= PT64_ROOT_LEVEL && level > 0);

	if (level == 1)
		memset((void *)__va(page_hpa), 0, PAGE_SIZE);
	else {
		u64 *pos;
		u64 *end;

		for (pos = (u64 *)__va(page_hpa), end = pos + PT64_ENT_PER_PAGE;
		     pos != end; pos++) {
			u64 current_ent = *pos;

			*pos = 0;
			if (is_present_pte(current_ent))
				release_pt_page_64(vcpu,
						  current_ent &
						  PT64_BASE_ADDR_MASK,
						  level - 1);
		}
	}
	kvm_mmu_free_page(vcpu, page_hpa);
}


static void nonpaging_flush(struct kvm_vcpu *vcpu)
{
	hpa_t root = vcpu->mmu.root_hpa;

	//++kvm_stat.tlb_flush;
	//pgprintk("nonpaging_flush\n");
	ASSERT(VALID_PAGE(root));
	release_pt_page_64(vcpu, root, vcpu->mmu.shadow_root_level);
	root = kvm_mmu_alloc_page(vcpu, NULL);
	ASSERT(VALID_PAGE(root));
	vcpu->mmu.root_hpa = root;
	if (is_paging(vcpu))
		root |= (vcpu->cr3 & (CR3_PCD | CR3_PWT));
	
	//kvm_arch_ops->set_cr3(vcpu, root);
	guest_CR3 = (u32)root;
	//kvm_arch_ops->tlb_flush(vcpu);
}


static void mark_pagetable_nonglobal(struct kvm_vcpu *vcpu, void *shadow_pte)
{
	page_header(vcpu, __pa(shadow_pte))->global = 0;
}


static inline void set_pte_common(struct kvm_vcpu *vcpu,
			     u64 *shadow_pte,
			     gpa_t gaddr,
			     int dirty,
			     u64 access_bits)
{
	hpa_t paddr;

	*shadow_pte |= access_bits << PT_SHADOW_BITS_OFFSET;
	if (!dirty)
		access_bits &= ~PT_WRITABLE_MASK;

	//if (access_bits & PT_WRITABLE_MASK)
	//	mark_page_dirty(vcpu->kvm, gaddr >> PAGE_SHIFT);

	*shadow_pte |= access_bits;

	paddr = gpa_to_hpa(vcpu, gaddr & PT64_BASE_ADDR_MASK);

	if (!(*shadow_pte & PT_GLOBAL_MASK))
		mark_pagetable_nonglobal(vcpu, shadow_pte);

	//if (is_error_hpa(paddr)) {
	//	*shadow_pte |= gaddr;
	//	*shadow_pte |= PT_SHADOW_IO_MARK;
	//	*shadow_pte &= ~PT_PRESENT_MASK;
	//} else {
		*shadow_pte |= paddr;
		//page_header_update_slot(vcpu->kvm, shadow_pte, gaddr);
	//}
}


static void FNAME(set_pte)(struct kvm_vcpu *vcpu, u64 guest_pte,
			   u64 *shadow_pte, u64 access_bits)
{
	ASSERT(*shadow_pte == 0);
	access_bits &= guest_pte;
	*shadow_pte = (guest_pte & PT_PTE_COPY_MASK);
	set_pte_common(vcpu, shadow_pte, guest_pte & PT_BASE_ADDR_MASK,
		       guest_pte & PT_DIRTY_MASK, access_bits);
}

static void FNAME(set_pde)(struct kvm_vcpu *vcpu, u64 guest_pde,
			   u64 *shadow_pte, u64 access_bits,
			   int index)
{
	gpa_t gaddr;

	ASSERT(*shadow_pte == 0);
	access_bits &= guest_pde;
	gaddr = (guest_pde & PT_DIR_BASE_ADDR_MASK) + PAGE_SIZE * index;
	if (PTTYPE == 32 && is_cpuid_PSE36())
		gaddr |= (guest_pde & PT32_DIR_PSE36_MASK) <<
			(32 - PT32_DIR_PSE36_SHIFT);
	*shadow_pte = guest_pde & PT_PTE_COPY_MASK;
	set_pte_common(vcpu, shadow_pte, gaddr,
		       guest_pde & PT_DIRTY_MASK, access_bits);
}





static void FNAME(init_walker)(struct guest_walker *walker,
			       struct kvm_vcpu *vcpu)
{
	hpa_t hpa;
	//struct kvm_memory_slot *slot;

	walker->level = vcpu->mmu.root_level;
	//slot = gfn_to_memslot(vcpu->kvm,
	//		      (vcpu->cr3 & PT64_BASE_ADDR_MASK) >> PAGE_SHIFT);
	hpa = safe_gpa_to_hpa(vcpu, vcpu->cr3 & PT64_BASE_ADDR_MASK);
	walker->table = (pt_element_t *)kmap_atomic(pfn_to_page(hpa >> PAGE_SHIFT), KM_USER0);

	ASSERT( (!is_long_mode(vcpu) && is_pae(vcpu)) ||
	        ((vcpu->cr3 & ~(PAGE_MASK | CR3_FLAGS_MASK)) == 0) );

	walker->table = (pt_element_t *)( (unsigned long)walker->table |
		(unsigned long)(vcpu->cr3 & ~(PAGE_MASK | CR3_FLAGS_MASK)) );
	walker->inherited_ar = PT_USER_MASK | PT_WRITABLE_MASK;
}

static void FNAME(release_walker)(struct guest_walker *walker)
{
	kunmap_atomic(walker->table, KM_USER0);
}

//PF handler code

/*
 * Fetch a guest pte from a specific level in the paging hierarchy.
 */
static pt_element_t *FNAME(fetch_guest)(struct kvm_vcpu *vcpu,
					struct guest_walker *walker,
					int level,
					gva_t addr)
{

	ASSERT(level > 0  && level <= walker->level);

	for (;;) {
		int index = PT_INDEX(addr, walker->level);
		hpa_t paddr;

		ASSERT(((unsigned long)walker->table & PAGE_MASK) ==
		       ((unsigned long)&walker->table[index] & PAGE_MASK));
		if (level == walker->level ||
		    !is_present_pte(walker->table[index]) ||
		    (walker->level == PT_DIRECTORY_LEVEL &&
		     (walker->table[index] & PT_PAGE_SIZE_MASK) &&
		     (PTTYPE == 64 || is_pse(vcpu))))
			return &walker->table[index];
		if (walker->level != 3 || is_long_mode(vcpu))
			walker->inherited_ar &= walker->table[index];
		paddr = safe_gpa_to_hpa(vcpu, walker->table[index] & PT_BASE_ADDR_MASK);
		kunmap_atomic(walker->table, KM_USER0);
		walker->table = (pt_element_t *)kmap_atomic(pfn_to_page(paddr >> PAGE_SHIFT),
					    KM_USER0);
		--walker->level;
	}
}


/*
 * The guest faulted for write.  We need to
 *
 * - check write permissions
 * - update the guest pte dirty bit
 * - update our own dirty page tracking structures
 */
static int FNAME(fix_write_pf)(struct kvm_vcpu *vcpu,
			       u64 *shadow_ent,
			       struct guest_walker *walker,
			       gva_t addr,
			       int user)
{
	pt_element_t *guest_ent;
	int writable_shadow;
	//gfn_t gfn;

	if (is_writeble_pte(*shadow_ent))
		return 0;

	writable_shadow = *shadow_ent & PT_SHADOW_WRITABLE_MASK;
	if (user) {
		/*
		 * User mode access.  Fail if it's a kernel page or a read-only
		 * page.
		 */
		if (!(*shadow_ent & PT_SHADOW_USER_MASK) || !writable_shadow)
			return 0;
		ASSERT(*shadow_ent & PT_USER_MASK);
	} else
		/*
		 * Kernel mode access.  Fail if it's a read-only page and
		 * supervisor write protection is enabled.
		 */
		if (!writable_shadow) {
			if (is_write_protection(vcpu))
				return 0;
			*shadow_ent &= ~PT_USER_MASK;
		}

	guest_ent = (pt_element_t *)FNAME(fetch_guest)(vcpu, walker, PT_PAGE_TABLE_LEVEL, addr);

	if (!is_present_pte(*guest_ent)) {
		*shadow_ent = 0;
		return 0;
	}

	//gfn = (*guest_ent & PT64_BASE_ADDR_MASK) >> PAGE_SHIFT;
	//mark_page_dirty(vcpu->kvm, gfn);
	*shadow_ent |= PT_WRITABLE_MASK;
	*guest_ent |= PT_DIRTY_MASK;

	return 1;
}

static void inject_page_fault(struct kvm_vcpu *vcpu,
			      u64 addr,
			      u32 err_code)
{
	//kvm_arch_ops->inject_page_fault(vcpu, addr, err_code);
	vmx_inject_exception_PF((u32)addr, err_code);
	guest_CR2 = (u32)addr;
}


static inline int fix_read_pf(u64 *shadow_ent)
{
	if ((*shadow_ent & PT_SHADOW_USER_MASK) &&
	    !(*shadow_ent & PT_USER_MASK)) {
		/*
		 * If supervisor write protect is disabled, we shadow kernel
		 * pages as user pages so we can trap the write access.
		 */
		*shadow_ent |= PT_USER_MASK;
		*shadow_ent &= ~PT_WRITABLE_MASK;

		return 1;

	}
	return 0;
}

/*
 * Fetch a shadow pte for a specific level in the paging hierarchy.
 */
static u64 *FNAME(fetch)(struct kvm_vcpu *vcpu, gva_t addr,
			      struct guest_walker *walker)
{
	hpa_t shadow_addr;
	int level;
	u64 *prev_shadow_ent = NULL;

	shadow_addr = vcpu->mmu.root_hpa;
	level = vcpu->mmu.shadow_root_level;

	for (; ; level--) {
		u32 index = SHADOW_PT_INDEX(addr, level);
		u64 *shadow_ent = ((u64 *)__va(shadow_addr)) + index;
		pt_element_t *guest_ent;
		u64 shadow_pte;

		if (is_present_pte(*shadow_ent) || is_io_pte(*shadow_ent)) {
			if (level == PT_PAGE_TABLE_LEVEL)
				return shadow_ent;
			shadow_addr = *shadow_ent & PT64_BASE_ADDR_MASK;
			prev_shadow_ent = shadow_ent;
			continue;
		}

		if (PTTYPE == 32 && level > PT32_ROOT_LEVEL) {
			ASSERT(level == PT32E_ROOT_LEVEL);
			guest_ent = FNAME(fetch_guest)(vcpu, walker,
						       PT32_ROOT_LEVEL, addr);
		} else
			guest_ent = FNAME(fetch_guest)(vcpu, walker,
						       level, addr);

		if (!is_present_pte(*guest_ent))
			return NULL;

		/* Don't set accessed bit on PAE PDPTRs */
		if (vcpu->mmu.root_level != 3 || walker->level != 3)
			*guest_ent |= PT_ACCESSED_MASK;

		if (level == PT_PAGE_TABLE_LEVEL) {

			if (walker->level == PT_DIRECTORY_LEVEL) {
				if (prev_shadow_ent)
					*prev_shadow_ent |= PT_SHADOW_PS_MARK;
				FNAME(set_pde)(vcpu, *guest_ent, shadow_ent,
					       walker->inherited_ar,
				          PT_INDEX(addr, PT_PAGE_TABLE_LEVEL));
			} else {
				ASSERT(walker->level == PT_PAGE_TABLE_LEVEL);
				FNAME(set_pte)(vcpu, *guest_ent, shadow_ent, walker->inherited_ar);
			}
			return shadow_ent;
		}

		shadow_addr = kvm_mmu_alloc_page(vcpu, shadow_ent);
		if (!VALID_PAGE(shadow_addr))
			return ERR_PTR(-ENOMEM);
		shadow_pte = shadow_addr | PT_PRESENT_MASK;
		if (vcpu->mmu.root_level > 3 || level != 3)
			shadow_pte |= PT_ACCESSED_MASK
				| PT_WRITABLE_MASK | PT_USER_MASK;
		*shadow_ent = shadow_pte;
		prev_shadow_ent = shadow_ent;
	}
}


/*
 * Page fault handler.  There are several causes for a page fault:
 *   - there is no shadow pte for the guest pte
 *   - write access through a shadow pte marked read only so that we can set
 *     the dirty bit
 *   - write access to a shadow pte marked read only so we can update the page
 *     dirty bitmap, when userspace requests it
 *   - mmio access; in this case we will never install a present shadow pte
 *   - normal guest page fault due to the guest pte marked not present, not
 *     writable, or not executable
 *
 *  Returns: 1 if we injected a guest PF, 0 otherwise
 */
static int FNAME(page_fault)(struct kvm_vcpu *vcpu, gva_t addr,
			       u32 error_code)
{
	int write_fault = error_code & PFERR_WRITE_MASK;
	int pte_present = error_code & PFERR_PRESENT_MASK;
	int user_fault = error_code & PFERR_USER_MASK;
	struct guest_walker walker;
	u64 *shadow_pte;
	int fixed;

	/*
	 * Look up the shadow pte for the faulting address.
	 */
	for (;;) {
		FNAME(init_walker)(&walker, vcpu);
		shadow_pte = FNAME(fetch)(vcpu, addr, &walker);
		printf("\n	shadow_ptr=0x%08x", (u32)shadow_pte);
		if (IS_ERR(shadow_pte)) {  /* must be -ENOMEM */
			printf("\n	PF: ENOMEM");
			nonpaging_flush(vcpu);
			FNAME(release_walker)(&walker);
			continue;
		}
		break;
	}

	/*
	 * The page is not mapped by the guest.  Let the guest handle it.
	 */
	if (!shadow_pte) {
		inject_page_fault(vcpu, addr, error_code);
		FNAME(release_walker)(&walker);
		printf("\n	PF: injecting to guest");
		return 1;
	}

	/*
	 * Update the shadow pte.
	 */
	if (write_fault)
		fixed = FNAME(fix_write_pf)(vcpu, shadow_pte, &walker, addr,
					    user_fault);
	else
		fixed = fix_read_pf(shadow_pte);

	FNAME(release_walker)(&walker);

	/*
	 * mmio: emulate if accessible, otherwise its a guest fault.
	 */
	//if (is_io_pte(*shadow_pte)) {
	//	if (may_access(*shadow_pte, write_fault, user_fault))
	//		return 1;
	//	pgprintk("%s: io work, no access\n", __FUNCTION__);
	//	inject_page_fault(vcpu, addr,
	//			  error_code | PFERR_PRESENT_MASK);
	//	return 0;
	//}

	/*
	 * pte not present, guest page fault.
	 */
	if (pte_present && !fixed) {
		inject_page_fault(vcpu, addr, error_code);
		printf("\n	PF: injecting to guest");
		return 1;
	}

	//++kvm_stat.pf_fixed;
	printf("\n	PF: cancelling");
	return 0;
}


/*
 * Remove a shadow pte.
 */
static void paging_inval_page(struct kvm_vcpu *vcpu, gva_t addr)
{
	hpa_t page_addr = vcpu->mmu.root_hpa;
	int level = vcpu->mmu.shadow_root_level;

	//++kvm_stat.invlpg;

	for (; ; level--) {
		u32 index = PT64_INDEX(addr, level);
		u64 *table = (u64 *)__va(page_addr);

		if (level == PT_PAGE_TABLE_LEVEL ) {
			table[index] = 0;
			return;
		}

		if (!is_present_pte(table[index]))
			return;

		page_addr = table[index] & PT64_BASE_ADDR_MASK;

		if (level == PT_DIRECTORY_LEVEL &&
			  (table[index] & PT_SHADOW_PS_MARK)) {
			table[index] = 0;
			release_pt_page_64(vcpu, page_addr, PT_PAGE_TABLE_LEVEL);

			//kvm_arch_ops->tlb_flush(vcpu);
			return;
		}
	}
}

static void kvm_mmu_flush_tlb(struct kvm_vcpu *vcpu)
{
	struct kvm_mmu_page *page, *npage;

	list_for_each_entry_safe(page, npage, &vcpu->kvm->active_mmu_pages,
				 link) {
		if (page->global)
			continue;

		if (!page->parent_pte)
			continue;

		*page->parent_pte = 0;
		release_pt_page_64(vcpu, page->page_hpa, 1);
	}
	//++kvm_stat.tlb_flush;
	//kvm_arch_ops->tlb_flush(vcpu);
}


static void paging_new_cr3(struct kvm_vcpu *vcpu)
{
	kvm_mmu_flush_tlb(vcpu);
}



void vcpu_populate(struct kvm_vcpu *vcpu){
	vcpu->cr0 = guest_CR0;
	vcpu->cr3 = shadow_guest_CR3;
	vcpu->cr4 = guest_CR4;
	

}


//------------------------------------------------------------------------------
// #PF handling
u32 shadow_page_fault(u32 cr2, u32 error_code){
	//populate vcpu
	vcpu_populate(&vcpu);
	vcpu.cr2 = cr2;
	
	printf("\n#PF: addr=0x%08x, e=0x%08x, vcpu->cr3=0x%08x, gCR3=0x%08x", cr2, error_code, vcpu.cr3,
		guest_CR3);
	//printf("\n	Assertion: 1v=%u, 2v=%u", (!is_long_mode(&vcpu) && is_pae(&vcpu)),
	//      ((vcpu.cr3 & ~(PAGE_MASK | CR3_FLAGS_MASK)) == 0) );
	return ( vcpu.mmu.page_fault(&vcpu, (gva_t)cr2,
			       error_code) );
	

	//return VMX_EVENT_INJECT;
}

//------------------------------------------------------------------------------
// INVLPG handling
void shadow_invalidate_page(u32 address){
	//populate vcpu
	vcpu_populate(&vcpu);

	vcpu.mmu.inval_page(&vcpu, address);
	return;
}


//------------------------------------------------------------------------------
//CR3 load handling
u32 shadow_new_context(u32 guest_CR3){
	struct kvm_mmu *context = &vcpu.mmu;

	//printf("\n0x%04x:0x%08x: MOV CR3, x (CR3 value=0x%08x)", 
	//	(unsigned short)guest_CS_selector, (unsigned int)guest_RIP, 
	//	(unsigned int)guest_CR3);
	
	//store original guest CR3 in our shadow variable
	shadow_guest_CR3 = guest_CR3;
	
	//populate vcpu
	vcpu_populate(&vcpu);

	vcpu.mmu.new_cr3(&vcpu);
	
	
	printf("\nMOV CR3, x: o=0x%08x, returning=0x%08x", shadow_guest_CR3, 
		context->root_hpa | (vcpu.cr3 & (CR3_PCD | CR3_PWT)));

	return ( context->root_hpa |
		    (vcpu.cr3 & (CR3_PCD | CR3_PWT)) );

	//return guest_CR3;
}


//initialization
static int paging32_init_context(struct kvm_vcpu *vcpu)
{
	struct kvm_mmu *context = &vcpu->mmu;

	context->new_cr3 = paging_new_cr3;
	context->page_fault = paging32_page_fault;
	context->inval_page = paging_inval_page;
	//context->gva_to_gpa = paging32_gva_to_gpa;
	//context->free = paging_free;
	context->root_level = PT32_ROOT_LEVEL;
	context->shadow_root_level = PT32E_ROOT_LEVEL;
	context->root_hpa = kvm_mmu_alloc_page(vcpu, NULL);
	ASSERT(VALID_PAGE(context->root_hpa));
	//kvm_arch_ops->set_cr3(vcpu, context->root_hpa |
	//	    (vcpu->cr3 & (CR3_PCD_MASK | CR3_WPT_MASK)));
	return 0;
}

static int init_kvm_mmu(struct kvm_vcpu *vcpu)
{
	ASSERT(vcpu);
	ASSERT(!VALID_PAGE(vcpu->mmu.root_hpa));

	//if (!is_paging(vcpu))
	//	return nonpaging_init_context(vcpu);
	//else if (is_long_mode(vcpu))
	//	return paging64_init_context(vcpu);
	//else if (is_pae(vcpu))
	//	return paging32E_init_context(vcpu);
	//else
	//	return paging32_init_context(vcpu);
		
	paging32_init_context(vcpu);
}

int kvm_mmu_setup(struct kvm_vcpu *vcpu)
{
	ASSERT(vcpu);
	ASSERT(!VALID_PAGE(vcpu->mmu.root_hpa));
	ASSERT(!list_empty(&vcpu->free_pages));

	return init_kvm_mmu(vcpu);
}

static int alloc_mmu_pages(struct kvm_vcpu *vcpu)
{
	int i;

	ASSERT(vcpu);

	for (i = 0; i < KVM_NUM_MMU_PAGES; i++) {
		//struct page *page;
		struct kvm_mmu_page *page_header = &vcpu->page_header_buf[i];

		INIT_LIST_HEAD(&page_header->link);
		//if ((page = alloc_page(GFP_KVM_MMU)) == NULL)
		//	goto error_1;
		//page->private = (unsigned long)page_header;
		vcpu->page_private[i] = (unsigned long)page_header;
		
		//page_header->page_hpa = (hpa_t)page_to_pfn(page) << PAGE_SHIFT;
		page_header->page_hpa = (hpa_t)( (u32)__shadow_alg0_area + (i*4096) );
		memset((void *)__va(page_header->page_hpa), 0, PAGE_SIZE);
		list_add(&page_header->link, &vcpu->free_pages);
	}
	return 0;

//error_1:
//	free_mmu_pages(vcpu);
//	return -ENOMEM;
}


int kvm_mmu_create(struct kvm_vcpu *vcpu)
{
	ASSERT(vcpu);
	ASSERT(!VALID_PAGE(vcpu->mmu.root_hpa));
	ASSERT(list_empty(&vcpu->free_pages));

	return alloc_mmu_pages(vcpu);
}


void shadow_alg0_initialize(void){
	memset( (void *)&vcpu, 0, sizeof(struct kvm_vcpu));
	memset( (void *)&kvm, 0, sizeof(struct kvm));
	
	INIT_LIST_HEAD(&kvm.active_mmu_pages);
	vcpu.mmu.root_hpa = INVALID_PAGE;
	INIT_LIST_HEAD(&vcpu.free_pages);
	vcpu.kvm = &kvm;


	kvm_mmu_create(&vcpu);

	kvm_mmu_setup(&vcpu);

}
