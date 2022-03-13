#include <xmhf.h>

XMHFList* xmhfstl_list_create(void)
{
    XMHFList* result = (XMHFList*)xmhf_mm_malloc(sizeof(XMHFList));
	if(!result)
		return NULL;
	result->count = 0;
	result->first = NULL;
	result->last = NULL;
	return result;
}

void xmhfstl_list_destroy(XMHFList *list)
{
	XMHFListNode *iter = NULL, *cur = NULL, *next = NULL;
	if(!list)
		return;
	
    iter = xmhfstl_list_first(list);
	
	while((iter != NULL))
	{
		cur = iter;
		next = iter->next;

		if(cur)
		{
			cur->prev = NULL;
			cur->next = NULL;
			xmhf_mm_free(cur);
		}
		iter = next;
	}

    xmhf_mm_free(list);
}

void xmhfstl_list_clear(XMHFList *list)
{
	if(!list)
		return;

	{ // due to the "mixed declarations and code" warning
	    XMHFLIST_FOREACH(list, first, next, cur) 
		{
			if(cur->value)
	       		xmhf_mm_free(cur->value);
	    }
	}
}

void xmhfstl_list_clear_destroy(XMHFList *list)
{
    xmhfstl_list_clear(list);
    xmhfstl_list_destroy(list);
}

XMHFListNode* xmhfstl_list_push(XMHFList *list, void *value)
{
    XMHFListNode* node = NULL;
	
	if(!list)
		return NULL;
	
	node = (XMHFListNode*)xmhf_mm_malloc(sizeof(XMHFListNode));
	if(!node)
		return NULL;
	
	node->next = NULL;
    node->value = value;

    if(list->last == NULL) {
        list->first = node;
        list->last = node;
    } else {
        list->last->next = node;
        node->prev = list->last;
        list->last = node;
    }

    list->count++;

//error:
    return node;
}

void* xmhfstl_list_pop(XMHFList *list)
{
	XMHFListNode *node;
	
	if(!list)
		return NULL;
	
    node = list->last;
    return node != NULL ? xmhfstl_list_remove(list, node) : NULL;
}

void* xmhfstl_list_dequeue(XMHFList *list)
{
	XMHFListNode *node;
	
	if(!list)
		return NULL;
	
    node = list->first;
    return node != NULL ? xmhfstl_list_remove(list, node) : NULL;
}


XMHFListNode* xmhfstl_list_last(XMHFList *list)
{
	XMHFListNode *node;
	
	if(!list)
		return NULL;
	
    node = list->last;
    return node;
}

XMHFListNode* xmhfstl_list_first(XMHFList *list)
{
	XMHFListNode *node;
	
	if(!list)
		return NULL;
	
    node = list->first;
    return node;
}

void* xmhfstl_list_remove(XMHFList *list, XMHFListNode *node)
{
    void *result = NULL;

	if(!list || !node)
		return NULL;

    //check(list->first && list->last, "XMHFList is empty.");
    //check(node, "node can't be NULL");

    if(node == list->first && node == list->last) {
        list->first = NULL;
        list->last = NULL;
    } else if(node == list->first) {
        list->first = node->next;
        //check(list->first != NULL, "Invalid list, somehow got a first that is NULL.");
        list->first->prev = NULL;
    } else if (node == list->last) {
        list->last = node->prev;
        //check(list->last != NULL, "Invalid list, somehow got a next that is NULL.");
        list->last->next = NULL;
    } else {
        XMHFListNode *after = node->next;
        XMHFListNode *before = node->prev;
        after->prev = before;
        before->next = after;
    }

    list->count--;
    result = node->value;
    xmhf_mm_free(node);

//error:
    return result;
}
