#pragma once

#include "key_def.h"
#include "small/rlist.h"
#include "stdint.h"

#ifdef __cplusplus
#include <map>
#endif

#ifdef __cplusplus
extern "C" {
#endif

enum dup_replace_mode {
	DUP_REPLACE_OR_INSERT,
	DUP_INSERT,
	DUP_REPLACE
};

struct tuple;
struct memtx_space;

struct index {
	/** Space id. */
	struct memtx_space *space;
	/** Index key definition. */
	key_def _key_def;
	/** Globally unique ID. */
	uint32_t unique_id;
	/** Compact ID - index in space->index array. */
	uint32_t dense_id;
    /*
	 * Зафиксированные случаи, отсутствия ключа в момент выполнения REPLACE,
	 * элемент был самым правым в индексе в момент вставки.
	 */
	struct rlist read_gaps;
#ifdef __cplusplus
	std::map<int, struct tuple *> tree;
#endif
};

struct key_or_null {
	int key;
	bool is_null;
};

enum iterator_type {
	ITER_EQ               =  0, /* key == x ASC order                  */
	ITER_REQ              =  1, /* key == x DESC order                 */
	ITER_ALL              =  2, /* all tuples                          */
	ITER_LT               =  3, /* key <  x                            */
	ITER_LE               =  4, /* key <= x                            */
	ITER_GE               =  5, /* key >= x                            */
	ITER_GT               =  6, /* key >  x                            */
	iterator_type_MAX
};

struct iterator {
	struct index *index;
	int (*next_internal)(struct iterator *it, struct tuple **ret);
	#ifdef __cplusplus
		std::map<int, struct tuple *>::iterator tree_iterator;
	#endif
	enum iterator_type type;
	//struct memtx_tree_key_data<USE_HINT> after_data;
	//struct memtx_tree_key_data<USE_HINT> key_data;
	struct key_or_null key_data;
	struct tuple *last_tuple;
};

int
index_check_dup(struct index *index, struct tuple *old_tuple, struct tuple *new_tuple, struct tuple *dup_tuple, enum dup_replace_mode mode);

int
index_get_internal(struct index *index, int key, struct tuple **result);

int
index_get(struct index *index, int key, struct tuple **result);

int
index_replace(struct index *index, struct tuple *old_tuple, struct tuple *new_tuple, enum dup_replace_mode mode, struct tuple **result, struct tuple **successor);

/**
 * Determine whether direction of given iterator type is reverse,
 * That is true for REQ, LT and LE etc and false for all others.
 */
static inline bool
iterator_type_is_reverse(enum iterator_type type)
{
	const unsigned reverse = (1u << ITER_REQ) | (1u << ITER_LT) | (1u << ITER_LE);
	return reverse & (1u << type);
}

/**
 * Determine a direction of given iterator type.
 * That is -1 for REQ, LT and LE etc and +1 for all others.
 */
static inline int
iterator_direction(enum iterator_type type)
{
	return iterator_type_is_reverse(type) ? -1 : 1;
}
int
iterator_next_internal(struct iterator *it, struct tuple **ret);

struct iterator *
index_create_iterator(struct index *index, enum iterator_type type, struct key_or_null key);

struct index *
index_new();

#ifdef __cplusplus
} // extern "C"
#endif
