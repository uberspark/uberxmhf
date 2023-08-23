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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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

// xmhf-lru.u
// Provide a template for implementing fully associative software LRU cache
// author: Eric Li (xiaoyili@andrew.cmu.edu)

/*
 * Create a new type (LRU_LINE_TYPE) for storing a cache line and a new type
 * (LRU_SET_TYPE) for storing a cache set. LRU_INDEX_TYPE needs to be able to
 * hold integers in [0, LRU_SIZE].
 */
#define LRU_NEW_SET(LRU_SET_TYPE, LRU_LINE_TYPE, LRU_SIZE, LRU_INDEX_TYPE, \
					LRU_KEY_TYPE, LRU_VALUE_TYPE) \
	typedef struct LRU_LINE_TYPE { \
		/*
		 * If 0, cache line is invalid. Otherwise, track LRU order (1 is most
		 * recently used; when all valid, LRU_SIZE is LRU).
		 *
		 * When considering the valid fields of all lines in a set, the
		 * non-zero values never repeat and are within 1 and LRU_SIZE
		 * (inclusive).
		 */ \
		LRU_INDEX_TYPE valid; \
		/* The key to determine whether cache matches, using operator "==" */ \
		LRU_KEY_TYPE key; \
		/* The value of the cache */ \
		LRU_VALUE_TYPE value; \
	} LRU_LINE_TYPE; \
	\
	typedef struct LRU_SET_TYPE { \
		LRU_LINE_TYPE elems[LRU_SIZE]; \
	} LRU_SET_TYPE;

/*
 * Iterate through all lines in a set using a forloop.
 * CUR_INDEX is a variable of type LRU_INDEX_TYPE to hold the index.
 * CUR_LINE is a variable of type LRU_LINE_TYPE * to hold the object.
 * LRU_SET is the cache set to be iterated through of type LRU_SET_TYPE *.
 */
#define LRU_FOREACH(CUR_INDEX, CUR_LINE, LRU_SET) \
	for (CUR_INDEX = 0, CUR_LINE = &((LRU_SET)->elems[0]); \
		 CUR_INDEX < (sizeof((LRU_SET)->elems) / sizeof((LRU_SET)->elems[0])); \
		 CUR_INDEX++, CUR_LINE++)

/*
 * Initialize all lines in a cache set.
 * The type of LRU_SET is LRU_SET_TYPE *. It is the cache set to be initialized.
 */
#define LRU_SET_INIT(LRU_SET) \
	do { \
		typeof((LRU_SET)->elems[0].valid) _i; \
		typeof(&((LRU_SET)->elems[0])) _line; \
		LRU_FOREACH(_i, _line, LRU_SET) { \
			_line->valid = 0; \
		} \
	} while (0)

/*
 * Find a key KEY in cache set LRU_SET, without changing the cache state.
 * If a line is found, the pointer to the line is put in FOUND_LINE
 * (type LRU_LINE_TYPE *) and true is returned. Otherwise, false is returned.
 */
#define LRU_SET_FIND_IMMUTABLE(LRU_SET, KEY, FOUND_LINE) \
	({ \
		bool _ans = false; \
		typeof((LRU_SET)->elems[0].valid) _i; \
		LRU_FOREACH(_i, FOUND_LINE, LRU_SET) { \
			if ((FOUND_LINE)->valid && (FOUND_LINE)->key == (KEY)) { \
				_ans = true; \
				break; \
			} \
		} \
		_ans; \
	})

/*
 * Find a key KEY in cache set LRU_SET, updating the LRU order, evicting when
 * necessary. The pointer to the line found is returned (type LRU_LINE_TYPE *).
 * The index of the line is set in INDEX (type LRU_INDEX_TYPE).
 * When CACHE_HIT is false, the caller needs to initialize / re-initialize the
 * value of the line.
 */
#define LRU_SET_FIND_EVICT(LRU_SET, KEY, INDEX, CACHE_HIT) \
	({ \
		/* _nlines = LRU_SIZE */ \
		const typeof((LRU_SET)->elems[0].valid) _nlines = \
			(sizeof((LRU_SET)->elems) / sizeof((LRU_SET)->elems[0])); \
		/* Index to be returned */ \
		typeof((LRU_SET)->elems[0].valid) _ans_index = _nlines; \
		/* Index of invalid entry during search (more preferred than LRU) */ \
		typeof((LRU_SET)->elems[0].valid) _available_index = _nlines; \
		/* Index of LRU entry during search (less preferred than invalid) */ \
		typeof((LRU_SET)->elems[0].valid) _evict_index = _nlines; \
		/* When updating LRU order, do not exceed this amount */ \
		typeof((LRU_SET)->elems[0].valid) _max_valid = _nlines; \
		typeof((LRU_SET)->elems[0].valid) _index; \
		typeof(&((LRU_SET)->elems[0])) _line; \
		typeof(&((LRU_SET)->elems[0])) _ans_line = NULL; \
		bool _cache_hit = false; \
		LRU_FOREACH(_index, _line, LRU_SET) { \
			if (_line->valid == 0) { \
				_available_index = _index; \
			} else if (_line->valid == _nlines) { \
				_evict_index = _index; \
			} else if (_line->key == (KEY)) { \
				_cache_hit = true; \
				_ans_index = _index; \
				_ans_line = _line; \
				_max_valid = _line->valid; \
				break; \
			} \
		} \
		if (!_cache_hit) { \
			if (_available_index < _nlines) { \
				/* Cold miss */ \
				_ans_index = _available_index; \
			} else { \
				/* Capacity miss */ \
				_ans_index = _evict_index; \
			} \
			_ans_line = &((LRU_SET)->elems[_ans_index]); \
		} \
		/* Update LRU order */ \
		LRU_FOREACH(_index, _line, LRU_SET) { \
			if (_line->valid && _line->valid < _max_valid) { \
				_line->valid++; \
			} \
		} \
		_ans_line->valid = 1; \
		_ans_line->key = (KEY); \
		(INDEX) = _ans_index; \
		(CACHE_HIT) = _cache_hit; \
		_ans_line; \
	})

/*
 * Find a key KEY in cache set LRU_SET and invalidate it.
 * If a line is found, the pointer to the line is put in FOUND_LINE
 * (type LRU_LINE_TYPE *) and true is returned. Otherwise, false is returned.
 *
 * Note that when this function returns true, the returned line is already
 * invalidated (valid = 0). However, when race condition is not considered,
 * the caller can still safely inspect the value in FOUND_LINE.
 */
#define LRU_SET_INVALIDATE(LRU_SET, KEY, FOUND_LINE) \
	({ \
		bool _ans = false; \
		typeof((LRU_SET)->elems[0].valid) _i; \
		LRU_FOREACH(_i, FOUND_LINE, LRU_SET) { \
			if ((FOUND_LINE)->valid && (FOUND_LINE)->key == (KEY)) { \
				_ans = true; \
				(FOUND_LINE)->valid = 0; \
				break; \
			} \
		} \
		_ans; \
	})

/* Invalidate all cache lines in cache set LRU_SET */
#define LRU_SET_INVALIDATE_ALL(LRU_SET) \
	do { \
		typeof((LRU_SET)->elems[0].valid) _i; \
		typeof(&((LRU_SET)->elems[0])) _line; \
		LRU_FOREACH(_i, _line, LRU_SET) { \
			_line->valid = 0; \
		} \
	} while (0)
