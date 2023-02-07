#include <xmhf.h>

XMHFList* xmhfstl_list_create(void)
{
    XMHFList* result = (XMHFList*)xmhf_mm_malloc(sizeof(XMHFList));
	if(!result)
		return NULL;

	result->count = 0;
	result->in_iteration = false;
	result->first = NULL;
	result->last = NULL;

	return result;
}

void xmhfstl_list_destroy(XMHFList *list)
{
	XMHFListNode *iter, *cur, *next;
	
	if(!list)
		return;

	// Do nothing if <list> is in the middle of iteration
	if(list->in_iteration)
	{
		printf("[LIST-ERR] <list_destroy>: XMHFList cannot be destroyed during its iteration\n");
		return;
	}

	iter = xmhfstl_list_first(list);
	while((iter != NULL))
	{
		cur = iter;
		next = iter->next;

		if(cur)
		{
			cur->prev = NULL;
			cur->next = NULL;

			// xmhf_mm_free(cur, sizeof(XMHFListNode));
			xmhf_mm_free(cur);
		}
		iter = next;
	}

	// xmhf_mm_free(list, sizeof(XMHFList));
	xmhf_mm_free(list);
}

//! @brief Free value pointers of all nodes of a given list
void xmhfstl_list_clear(XMHFList *list)
{
	if(!list)
		return;

	// Do nothing if <list> is in the middle of iteration
	if(list->in_iteration)
	{
		printf("[LIST-ERR] <list_clear>: XMHFList cannot be modified during its iteration\n");
		return;
	}

	{
		XMHFLIST_FOREACH(list, first, next, cur) 
		{
			if((cur->type == LIST_ELEM_PTR) && (cur->value))
			{
				// xmhf_mm_free(MEM_KERNEL, cur->value, cur->mem_sz);
				xmhf_mm_free(cur->value);
			}

			cur->value = NULL;
			cur->mem_sz = 0;
			cur->type = LIST_ELEM_INVALID;
		}
		END_XMHFLIST_FOREACH(list);
	}
}

void xmhfstl_list_debug(XMHFList *list)
{
	int count = 0;
	if(!list)
		return;

	printf("Total count:%d\n", list->count);
	{
	    XMHFLIST_FOREACH(list, first, next, cur) {
			count++;
	        printf("[%d] (cur:0x%p, value:0x%p)<-->", count, cur, cur->value);
	    }
		END_XMHFLIST_FOREACH(list);
	}
	printf("\n");
}


void xmhfstl_list_clear_destroy(XMHFList *list)
{
    xmhfstl_list_clear(list);
    xmhfstl_list_destroy(list);
}

XMHFListNode* xmhfstl_list_push(XMHFList *list, void *value, size_t mem_sz, LIST_ELEM_TYPE type)
{
    XMHFListNode* node = NULL;
	
	if(!list)
		return NULL;

	// Do nothing if <list> is in the middle of iteration
	if(list->in_iteration)
	{
		printf("[LIST-ERR] <list_push>: XMHFList cannot be modified during its iteration\n");
		return NULL;
	}
	
	node = xmhf_mm_malloc(sizeof(XMHFListNode));
	if(!node)
		return NULL;
	
	node->next = NULL;
    node->value = value;
	node->mem_sz = mem_sz;
	node->type = type;

    if(list->last == NULL) {
        list->first = node;
        list->last = node;
    } else {
        list->last->next = node;
        node->prev = list->last;
        list->last = node;
    }

    list->count++;

    return node;
}

void* xmhfstl_list_pop(XMHFList *list)
{
	XMHFListNode *node;
	
	if(!list)
		return NULL;

	// Do nothing if <list> is in the middle of iteration
	if(list->in_iteration)
	{
		printf("[LIST-ERR] <list_pop>: XMHFList cannot be modified during its iteration\n");
		return NULL;
	}
	
    node = list->last;
    return node != NULL ? xmhfstl_list_remove(list, node) : NULL;
}

void* xmhfstl_list_dequeue(XMHFList *list)
{
	XMHFListNode *node;
	
	if(!list)
		return NULL;

	// Do nothing if <list> is in the middle of iteration
	if(list->in_iteration)
	{
		printf("[LIST-ERR] <list_dequeue>: XMHFList cannot be modified during its iteration\n");
		return NULL;
	}
	
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

XMHFListNode* xmhfstl_list_insert_before(XMHFList* list, XMHFListNode *node, void *value, size_t mem_sz)
{
	XMHFListNode* new_node = NULL;
	
	if(!list || !node)
		return NULL;

	// Do nothing if <list> is in the middle of iteration
	if(list->in_iteration)
	{
		printf("[LIST-ERR] <list_insert_before>: XMHFList cannot be modified during its iteration\n");
		return NULL;
	}

	new_node = xmhf_mm_malloc(sizeof(XMHFListNode));
	if(!new_node)
		return NULL;
	
    new_node->value = value;
	new_node->mem_sz = mem_sz;

	new_node->prev = node->prev;
	new_node->next = node;

	if(node->prev)
		node->prev->next = new_node;
	node->prev = new_node;

	list->count++;
	return new_node;
}

XMHFListNode* xmhfstl_list_insert_after(XMHFList* list, XMHFListNode *node, void *value, size_t mem_sz)
{
	XMHFListNode* new_node = NULL;
	
	if(!list || !node)
		return NULL;

	// Do nothing if <list> is in the middle of iteration
	if(list->in_iteration)
	{
		printf("[LIST-ERR] <list_insert_after>: XMHFList cannot be modified during its iteration\n");
		return NULL;
	}

	new_node = xmhf_mm_malloc(sizeof(XMHFListNode));
	if(!new_node)
		return NULL;
	
    new_node->value = value;
	new_node->mem_sz = mem_sz;

	new_node->next = node->next;
	new_node->prev = node;

	if(node->next)
		node->next->prev = new_node;
	node->next = new_node;

	list->count++;
	return new_node;
}


void* xmhfstl_list_remove(XMHFList *list, XMHFListNode *node)
{
    void *result = NULL;

	if(!list || !node)
		return NULL;

	// Do nothing if <list> is in the middle of iteration
	if(list->in_iteration)
	{
		printf("[LIST-ERR] <list_remove>: XMHFList cannot be modified during its iteration\n");
		return NULL;
	}

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
	
    // xmhf_mm_free(node, sizeof(XMHFListNode));
	xmhf_mm_free(node);

    return result;
}