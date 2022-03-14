// copy from http://c.learncodethehardway.org/book/ex32.html

#ifndef XMHF_STL_DOUBLE_LLIST
#define XMHF_STL_DOUBLE_LLIST

#ifndef __ASSEMBLY__

struct XMHFListNode;

typedef struct XMHFListNode {
    struct XMHFListNode *next;
    struct XMHFListNode *prev;
    void *value;
} XMHFListNode;

typedef struct XMHFList {
    int count;
    XMHFListNode *first;
    XMHFListNode *last;
} XMHFList;

extern XMHFList* xmhfstl_list_create(void);
extern void xmhfstl_list_destroy(XMHFList *list);
extern void xmhfstl_list_clear(XMHFList *list);
extern void xmhfstl_list_clear_destroy(XMHFList *list);

#define XMHFList_count(A) ((A)->count)
#define XMHFList_first(A) ((A)->first != NULL ? (A)->first->value : NULL)
#define XMHFList_last(A) ((A)->last != NULL ? (A)->last->value : NULL)
#define xmhfstl_list_enqueue(l, v) xmhfstl_list_push(l, v)
#define is_list_empty(l) (l->count == 0)

extern XMHFListNode* xmhfstl_list_push(XMHFList *list, void *value);
extern void* xmhfstl_list_pop(XMHFList *list);
extern void* xmhfstl_list_dequeue(XMHFList *list);

extern XMHFListNode* xmhfstl_list_last(XMHFList *list);
extern XMHFListNode* xmhfstl_list_first(XMHFList *list);


extern void xmhfstl_list_unshift(XMHFList *list, void *value);
extern void *xmhfstl_list_shift(XMHFList *list);

extern void *xmhfstl_list_remove(XMHFList *list, XMHFListNode *node);
extern void xmhfstl_list_debug(XMHFList *list);

#define XMHFLIST_FOREACH(L, S, M, V) XMHFListNode *_node = NULL;\
    XMHFListNode *V = NULL;\
    for(V = _node = L->S; _node != NULL; V = _node = _node->M)

#endif // __ASSEMBLY__
#endif // XMHF_STL_DOUBLE_LLIST
