/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

#ifndef LIST_H
#define LIST_H

/* loosely based on ch 7 of "C Interfaces and Implementations" by
   David Hanson */

typedef struct ll_t {
  void *first;
  struct ll_t *rest;
} ll_t;

__attribute__((unused))
static void* LL_first(ll_t *list)
{
  return list->first;
}

__attribute__((unused))
static ll_t* LL_rest(ll_t *list)
{
  return list->rest;
}

/* note- allocates memory. will return null if allocation fails */
__attribute__((unused))
static ll_t* LL_push(ll_t *list, void *first)
{
  ll_t *rv = malloc(sizeof(ll_t));
  if (rv != NULL) {
    *rv = (ll_t) {
      .first = first,
      .rest = list
    };
  }

  return rv;
}

/* destructive push. rewrite the list ptr to pt to the new head */
__attribute__((unused))
static ll_t* LL_dpush(ll_t **list, void *first)
{
  *list = LL_push(*list, first);
  return *list;
}

__attribute__((unused))
static ll_t* LL_pop(ll_t *list, void **x)
{
  ll_t *rest = NULL;

  if(list) {
    rest = list->rest;
    if (x) {
      *x = list->first;
    }
    free(list);
  }

  return rest;
}

/* frees the list structure itself, not the items in it */
__attribute__((unused))
static void LL_free(ll_t *list)
{
  while (list != NULL) {
    list = LL_pop(list, NULL);
  }
}

/* for loop. on each iteration x is set to the current head item, l is set to the current tail */
#define LL_FOR_EACH(l, x) for((x) = (l)->first ; (l) != NULL ; (x) = (l)->first, (l) = (l)->rest)



#endif
