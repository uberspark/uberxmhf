// copy from http://c.learncodethehardway.org/book/ex32.html

#ifndef XMHF_STL_DOUBLE_LLIST
#define XMHF_STL_DOUBLE_LLIST

#ifndef __ASSEMBLY__

struct XMHFListNode;

typedef enum {
    LIST_ELEM_INVALID = 0,
    LIST_ELEM_VAL = 1,
    LIST_ELEM_PTR = 2,
} LIST_ELEM_TYPE;

typedef struct XMHFListNode {
    struct XMHFListNode *next;
    struct XMHFListNode *prev;
    void *value;
    size_t mem_sz;
    LIST_ELEM_TYPE type;
} XMHFListNode;

typedef struct XMHFList {
    uint32_t	count;
	bool 		in_iteration;
    XMHFListNode*	first;
    XMHFListNode*	last;
} XMHFList;


extern XMHFList* xmhfstl_list_create(void);
extern void xmhfstl_list_destroy(XMHFList *list);

//! @brief Free value pointers of all nodes of a given list
extern void xmhfstl_list_clear(XMHFList *list);
extern void xmhfstl_list_clear_destroy(XMHFList *list);

#define XMHFList_count(l) ((l)->count)
#define XMHFList_first(l) ((l)->first != NULL ? (l)->first->value : NULL)
#define XMHFList_last(l) ((l)->last != NULL ? (l)->last->value : NULL)
#define xmhfstl_list_enqueue(l, v, sz, type) xmhfstl_list_push((l), (v), (sz), (type))
#define is_list_empty(l) (l->count == 0)

extern XMHFListNode* xmhfstl_list_push(XMHFList *list, void *value, size_t mem_sz, LIST_ELEM_TYPE type);
extern void* xmhfstl_list_pop(XMHFList *list);
extern void* xmhfstl_list_dequeue(XMHFList *list);

extern XMHFListNode* xmhfstl_list_last(XMHFList *list);
extern XMHFListNode* xmhfstl_list_first(XMHFList *list);

extern XMHFListNode* xmhfstl_list_insert_before(XMHFList* list, XMHFListNode *node, void *value, size_t mem_sz);
extern XMHFListNode* xmhfstl_list_insert_after(XMHFList* list, XMHFListNode *node, void *value, size_t mem_sz);

extern void* xmhfstl_list_remove(XMHFList *list, XMHFListNode *node);
extern void xmhfstl_list_debug(XMHFList *list);

// [TODO][Ticket 179] LIST_FOREACH needs to avoid list modification

#define XMHFLIST_FOREACH(L, S, M, V) XMHFListNode *_node = NULL;\
    XMHFListNode *V = NULL;\
    L->in_iteration = true; \
    for(V = _node = L->S; _node != NULL; V = _node = _node->M)

#define END_XMHFLIST_FOREACH(L) L->in_iteration = false;

#endif // __ASSEMBLY__
#endif // XMHF_STL_DOUBLE_LLIST
