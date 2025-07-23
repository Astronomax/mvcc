#include "index.h"
#include "memtx_tx.h"
#include "memtx_space.h"
#include "txn.h"
#include "stdbool.h"
#include <memory>
#include <stdexcept>

int
index_check_dup(struct index *index, struct tuple *old_tuple, struct tuple *new_tuple, struct tuple *dup_tuple, enum dup_replace_mode mode)
{
    /*
     * old_tuple - это тот тапл, который должен быть удален. Бывают случаи,
     * когда у нас откуда-то в момент вызова уже есть информация о том, что
     * мы собираемся удалить, например, в случае DELETE.
     *
     * Если это REPLACE и index - primary, то old_tuple == NULL.
     * Если это REPLACE и index - secondary, то old_tuple == visible(directly_replaced[0]) (
     * то, что увидел REPLACE в момент замены по первичному ключю).
     * 
     * Если это DELETE, то old_tuple == index_get_internal(pk), который был вызван до того
     * как выполнить REPLACE(old_tuple, NULL).
     */
	if (dup_tuple == NULL) {
		if (mode == DUP_REPLACE) { //при REPLACE, по первичному ключу передается mode == DUP_REPLACE
			assert(old_tuple != NULL);
			/* При DUP_REPLACE обязательно должна произойти замена, а не вставка. */
			fprintf(stderr, "Attempt to modify a tuple field which is part of primary index in space %s\n", "TODO");
			goto fail;
		}
	} else { /* dup_tuple != NULL */
		if (dup_tuple != old_tuple && (old_tuple != NULL || mode == DUP_INSERT)) { //а по всем вторичным - DUP_INSERT
            /*
             * Поэтому все вторичные ключи должны удалять то же самое, что первичный.
			 * Мы не можем удалить более чем один тапл за раз.
			 */
			fprintf(stderr, "Duplicate key exists in unique index \"%s\" in space \"%s\" with old tuple - %s and new tuple - %s\n", "TODO", "TODO", tuple_str(dup_tuple), tuple_str(new_tuple));
			goto fail;
		}
	}
	return 0;
fail:
	txn_set_flags(in_txn(), TXN_STMT_ROLLBACK);
	return -1;
}

int
index_get_internal(struct index *index, int key, struct tuple **result)
{
	struct txn *txn = in_txn();
	struct memtx_space *space = index->space;
	auto it = index->tree.find(key);
	if (it == index->tree.end()) {
		*result = NULL;
		memtx_tx_track_point(txn, space, index, key);
		return 0;
	}
	struct tuple *tuple = it->second;
	*result = memtx_tx_tuple_clarify(txn, space, tuple, index);
	return 0;
}

int
index_get(struct index *index, int key, struct tuple **result)
{
	return index_get_internal(index, key, result);
}

int
index_replace(struct index *index, struct tuple *old_tuple, struct tuple *new_tuple, enum dup_replace_mode mode, struct tuple **result, struct tuple **successor)
{
	key_def *key_def = &index->_key_def;
	if (new_tuple != NULL) {
		int key = new_tuple->data[*key_def];
		struct tuple *dup_tuple = NULL;
		auto it = index->tree.find(key);
		if (it != index->tree.end()) {
			dup_tuple = it->second;
			it->second = new_tuple;
		} else {
			it = index->tree.insert({key, new_tuple}).first;
		}
		if (index_check_dup(index, old_tuple, new_tuple, dup_tuple, mode) != 0) {
			if (dup_tuple != NULL)
				it->second = dup_tuple;
			else
				index->tree.erase(it);
			return -1;
		}
		if (++it != index->tree.end()) {
			*successor = it->second;
		} else {
			*successor = NULL;
		}
		if (dup_tuple != NULL) {
			*result = dup_tuple;
			return 0;
		}
	}
	if (old_tuple != NULL) {
		int key = old_tuple->data[*key_def];
		auto it = index->tree.find(key);
		if (it != index->tree.end())
			index->tree.erase(it);
		*result = old_tuple;
	} else {
		*result = NULL;
	}
	return 0;
}

static void
canonicalize_lookup(enum iterator_type *type, struct key_or_null *key/*, uint32_t part_count*/)
{
	assert(*type >= 0 && *type < iterator_type_MAX);

	/* Для простоты считаем, что part_count всего равен 0. */
	//if (part_count == 0) {
		/*
		 * If no key is specified, downgrade equality
		 * iterators to a full range.
		 */
		*type = iterator_type_is_reverse(*type) ? ITER_LE : ITER_GE;
		key->is_null = true;
	//}

	if (*type == ITER_ALL)
		*type = ITER_GE;
}

struct tuple *
memtx_tree_iterator_get_elem(std::map<int, struct tuple *> *tree, std::map<int, struct tuple *>::iterator *iterator)
{
	return ((*iterator == tree->end()) ? NULL : ((*iterator)->second));
}

static bool
memtx_tree_lookup(std::map<int, struct tuple *> *tree,
		  struct key_or_null *start_data, enum iterator_type *type,
		  std::map<int, struct tuple *>::iterator *iterator,
		  bool *equals, struct tuple **initial_elem)
{
	//struct key_def *cmp_def = memtx_tree_cmp_def(tree);

	/* У нас пока не поддерживаются ITER_NP и ITER_PP. */
	//if ((*type == ITER_NP || *type == ITER_PP) &&
	//    after_data.key == NULL) {
	//	if (!prepare_start_prefix_iterator(type, &start_data->key,
	//					   start_data->part_count,
	//					   cmp_def, region))
	//		return false;
	//	if (USE_HINT) {
	//		hint_t hint = key_hint(start_data->key,
	//				       start_data->part_count, cmp_def);
	//		start_data->set_hint(hint);
	//	}
	//}

	/*
	 * Since iteration with equality iterators returns first found tuple,
	 * we need a special flag for EQ and REQ if we want to start iteration
	 * after specified key (this flag will affect the choice between
	 * lower bound and upper bound for the above iterators).
	 * As for range iterators with equality, we can simply change them
	 * to their equivalents with inequality.
	 */
	/* Это пока что-то непонятное. */
	//bool skip_equal_tuple = after_data.key != NULL;
	//if (skip_equal_tuple && *type != ITER_EQ && *type != ITER_REQ)
	//	*type = iterator_type_is_reverse(*type) ? ITER_LT : ITER_GT;

	/* Perform the initial lookup. */
	if (start_data->is_null) {
		assert(*type == ITER_GE || *type == ITER_LE);
		if (iterator_type_is_reverse(*type)) {
			/*
			 * For all reverse iterators we will step back,
			 * see the and explanation code below.
			 * BPS tree iterators have an interesting property:
			 * a back step from invalid iterator set its
			 * position to the last element. Let's use that.
			 */
			/* В общем-то это справедливо и для std::map итератора. */
			//invalidate_tree_iterator(iterator);
			//*offset = memtx_tree_size(tree);
			*iterator = tree->end();
		} else {
			//*iterator = memtx_tree_first(tree);
			//*offset = 0;
			*iterator = tree->begin();
		}

		/* If there is at least one tuple in the tree, it is
		 * efficiently equals to the empty key. */
		//*equals = memtx_tree_size(tree) != 0;
		*equals = !tree->empty();
	} else {
		/*
		 * We use lower_bound on equality iterators instead of LE
		 * because if iterator is reversed, we will take a step back.
		 * Also it is used for LT iterator, and after a step back
		 * iterator will point to a tuple lower than key.
		 * So, lower_bound is used for EQ, GE and LT iterators,
		 * upper_bound is used for REQ, GT, LE iterators.
		 */
		bool need_lower_bound = *type == ITER_EQ || *type == ITER_GE || *type == ITER_LT;

		/*
		 * If we need to skip first tuple in EQ and REQ iterators,
		 * let's just change lower_bound to upper_bound or vice-versa.
		 */
		/* У нас пока что skip_equal_tuple == false всегда. */
		//if (skip_equal_tuple && (*type == ITER_EQ || *type == ITER_REQ))
		//	need_lower_bound = !need_lower_bound;

		if (need_lower_bound) {
			//*iterator = memtx_tree_lower_bound_get_offset(tree, start_data, equals, offset);
			*iterator = tree->lower_bound(start_data->key);
			*equals = (*iterator != tree->end()) && ((*iterator)->first == start_data->key);
		} else {
			//*iterator = memtx_tree_upper_bound_get_offset(tree, start_data, equals, offset);
			*iterator = tree->upper_bound(start_data->key);
			*equals = false;
		}
	}

	/* Save the element we approached on the initial lookup. */
	*initial_elem = memtx_tree_iterator_get_elem(tree, iterator);

	if (iterator_type_is_reverse(*type)) {
		/*
		 * Because of limitations of tree search API we use
		 * lower_bound for LT search and upper_bound for LE and
		 * REQ searches. In both cases we find a position to the
		 * right of the target one. Let's make a step to the
		 * left to reach target position.
		 * If we found an invalid iterator all the elements in
		 * the tree are less (less or equal) to the key, and
		 * iterator_prev call will convert the iterator to the
		 * last position in the tree, that's what we need.
		 */
		//memtx_tree_iterator_prev(tree, iterator);
		//--*offset; /* Unsigned underflow possible. */
		--iterator;
	}
	return true;
}

static inline void
tree_iterator_set_last(struct iterator *iterator, struct tuple *last_tuple)
{
	assert(last_tuple != NULL);
	iterator->last_tuple = last_tuple;
}

int
exhausted_iterator_next(struct iterator *it, struct tuple **ret)
{
	(void)it;
	*ret = NULL;
	return 0;
}

static void
tree_iterator_set_next_method(struct iterator *it);

static int
tree_iterator_start(struct iterator *iterator, struct tuple **ret)
{
	*ret = NULL;
	iterator->next_internal = exhausted_iterator_next;

	//assert(it->last.tuple == NULL);

	struct index *index = iterator->index;
	struct memtx_space *space = index->space;

	std::map<int, struct tuple *> *tree = &index->tree;
	struct key_or_null start_data = iterator->key_data;
	enum iterator_type type = iterator->type;
	/* The flag is true if the found tuple equals to the key. */
	bool equals;
	struct tuple *initial_elem_tuple;
	if (!memtx_tree_lookup(tree, &start_data, &type, &iterator->tree_iterator, &equals, &initial_elem_tuple))
		return 0;

	/*
	 * The initial element could potentially be a successor of the key: we
	 * need to track gap based on it.
	 */
	struct tuple *successor = initial_elem_tuple;

	struct tuple *res_tuple = initial_elem_tuple;
	/*
	 * If the iterator type is not reverse, the initial_elem is the result
	 * of the first iteration step. Otherwise the lookup function performs
	 * an extra step back, so we need to actualize the current element now.
	 */
	if (iterator_type_is_reverse(type))
		res_tuple = memtx_tree_iterator_get_elem(tree, &iterator->tree_iterator);

	/* Мы предполагаем, что offset итератора всегда равен 0 для простоты. */
	/* Skip the amount of tuples required. */
	struct txn *txn = in_txn();
	//if (it->offset != 0 && res != NULL) {
	//	/* Normalize the unsigned underflow to SIZE_MAX if expected. */
	//	size_t skip = it->offset;
	//	bool reverse = iterator_type_is_reverse(type);
	//	if (reverse && skip > curr_offset + 1)
	//		skip = curr_offset + 1;
	//
	//	/* Skip raw tuples and actualize the current element. */
	//	curr_offset = reverse ? curr_offset - skip : curr_offset + skip;
	//	it->tree_iterator = memtx_tree_iterator_at(tree, curr_offset);
	//	res = memtx_tree_iterator_get_elem(tree, &it->tree_iterator);
	//
	//	/*
	//	 * We have logarithmically skipped tuples, but some of them may
	//	 * be invisible to the current transaction. Let's skip further
	//	 * if required AND if we haven't reached the end of the index.
	//	 */
	//	size_t skip_more_visible = res == NULL ? 0 :
	//		memtx_tx_index_invisible_count_matching_until(
	//			txn, space, index_base, type, start_data.key,
	//			start_data.part_count, res->tuple, res->hint);
	//	memtx_tree_iterator_t<USE_HINT> *iterator = &it->tree_iterator;
	//	while (skip_more_visible != 0 && res != NULL) {
	//		if (memtx_tx_tuple_key_is_visible(txn, space,
	//						  index_base,
	//						  res->tuple))
	//			skip_more_visible--;
	//		if (reverse)
	//			memtx_tree_iterator_prev(tree, iterator);
	//		else
	//			memtx_tree_iterator_next(tree, iterator);
	//		res = memtx_tree_iterator_get_elem(tree, iterator);
	//	}
	//}

	bool is_eq = type == ITER_EQ || type == ITER_REQ;

	/*
	 * Для простоты предполагаем, что after_data.key == NULL и offset итератора
	 * равен 0 всегда.
	 */
	/* If we skip tuple, flag equals is not actual - need to refresh it. */
	//if (((it->after_data.key != NULL && is_eq) || it->offset != 0) &&
	//    res != NULL) {
	//	equals = tuple_compare_with_key(res->tuple, res->hint, it->key_data.key, it->key_data.part_count, it->key_data.hint, index->base.def->key_def) == 0;
	//}

	/*
	 * Equality iterators requires exact key match: if the result does not
	 * equal to the key, iteration ends.
	 */
	bool eq_match = equals || !is_eq;
	if (res_tuple != NULL && eq_match) {
		tree_iterator_set_last(iterator, res_tuple);
		tree_iterator_set_next_method(iterator);
		*ret = memtx_tx_tuple_clarify(txn, space, res_tuple, index);
	}

	/* Мы предполагаем, что offset итератора всегда равен 0 для простоты. */
	/*
	 * If the key is full then all parts present, so EQ and REQ iterators
	 * can return no more than one tuple.
	 */
	//struct key_def *cmp_def = index->base.def->cmp_def;
	//bool key_is_full = start_data.part_count == cmp_def->part_count;
	bool key_is_full = !start_data.is_null;
	//if (it->offset != 0) {
	//	if (res == NULL || !eq_match) {
	//		/*
	//		 * We have stepped over some amount of tuples and got to
	//		 * the end of the index or stepped over the matching set
	//		 * (if iterator is EQ or REQ). Lets inform MVCC like we
	//		 * have counted tuples in the index by our iterator and
	//		 * key. Insertion or deletion of any matching tuple into
	//		 * the index will conflict with us.
	//		 */
	//		memtx_tx_track_count(txn, space, index_base,
	//				     type, start_data.key,
	//				     start_data.part_count);
	//
	//	} else {
	//		/*
	//		 * We have stepped over some amount of tuples and got to
	//		 * a tuple. Changing the amount of matching tuples prior
	//		 * to the approached one must conflict with us, so lets
	//		 * inform MVCC like we have counted tuples in the index
	//		 * by our key and iterator until the approached tuple.
	//		 *
	//		 * The approached tuple itself is read above, so its
	//		 * replacement or deletion is tracked already.
	//		 */
	//		memtx_tx_track_count_until(txn, space, index_base,
	//					   type, start_data.key,
	//					   start_data.part_count,
	//					   res->tuple, res->hint);
	//	}
	//	/*
	//	 * We track all the skipped tuples using one of count trackers,
	//	 * so no extra tracking is required in this case, insertion or
	//	 * deletion of a matching tuple will be caught.
	//	 */
	//	goto end;
	//}
	if (key_is_full && !eq_match)
		memtx_tx_track_point(txn, space, index, iterator->key_data.key);
	/*
	 * Since MVCC operates with `key_def` of index but `start_data` can
	 * contain key extracted with `cmp_def`, we should crop it by passing
	 * `part_count` not greater than `key_def->part_count`.
	 */
	if (!key_is_full ||
	    ((type == ITER_GE || type == ITER_LE) && !equals) ||
	    (type == ITER_GT || type == ITER_LT))
		memtx_tx_track_gap(txn, space, index, successor, type, start_data);

end:

	return res_tuple == NULL || !eq_match || *ret != NULL ? 0 :
	       iterator->next_internal(iterator, ret);
}

struct iterator *
index_create_iterator(struct index *index, enum iterator_type type, struct key_or_null key)
{
	struct iterator *it = (struct iterator *)malloc(sizeof(struct iterator));
	if (it == NULL) {
		fprintf(stderr, "Failed to allocate %u bytes in %s for %s\n", sizeof(struct iterator), "memtx_tree_index", "iterator");
		return NULL;
	}
	canonicalize_lookup(&type, &key/*, part_count*/);
	it->index = index;
	it->next_internal = tree_iterator_start;
	it->type = type;
	//it->after_data.key = NULL;
	//it->after_data.part_count = 0;
	it->key_data = key;
	return it;
}

static int
tree_iterator_next_base(struct iterator *iterator, struct tuple **ret)
{
	struct index *index_base = iterator->index;
	struct memtx_space *space = iterator->index->space;
	iterator->tree_iterator++;
	struct tuple *res_tuple = NULL;
	struct txn *txn = in_txn();
	if (iterator->tree_iterator != iterator->index->tree.end())
		res_tuple = iterator->tree_iterator->second;
	*ret = res_tuple;
	if (*ret == NULL) {
		iterator->next_internal = exhausted_iterator_next;
	} else {
		tree_iterator_set_last(iterator, res_tuple);
		*ret = memtx_tx_tuple_clarify(txn, space, res_tuple, index_base);
	}
	/*
	 * Pass no key because any write to the gap between that
	 * two tuples must lead to conflict.
	 */
	struct tuple *successor = res_tuple;
	memtx_tx_track_gap(txn, space, index_base, successor, ITER_GE, key_or_null{0, true});
	return 0;
}

#define WRAP_ITERATOR_METHOD(name)											\
static int																	\
name(struct iterator *iterator, struct tuple **ret)							\
{																			\
	do {																	\
		int rc = name##_base(iterator, ret);								\
		if (rc != 0 || iterator->next_internal == exhausted_iterator_next)	\
			return rc;														\
	} while (*ret == NULL);													\
	return 0;																\
}

WRAP_ITERATOR_METHOD(tree_iterator_next);
//WRAP_ITERATOR_METHOD(tree_iterator_prev);
//WRAP_ITERATOR_METHOD(tree_iterator_next_equal);
//WRAP_ITERATOR_METHOD(tree_iterator_prev_equal);

#undef WRAP_ITERATOR_METHOD

static void
tree_iterator_set_next_method(struct iterator *it)
{
	switch (it->type) {
	case ITER_EQ:
		throw std::runtime_error("not implemented");
		//it->base.next_internal = tree_iterator_next_equal;
		break;
	case ITER_REQ:
		throw std::runtime_error("not implemented");
		//it->base.next_internal = tree_iterator_prev_equal;
		break;
	case ITER_LT:
	case ITER_LE:
		throw std::runtime_error("not implemented");
		//it->base.next_internal = tree_iterator_prev;
		break;
	case ITER_GE:
	case ITER_GT:
		it->next_internal = tree_iterator_next;
		break;
	default:
		/* The type was checked in initIterator */
		assert(false);
	}
	//it->base.next = memtx_iterator_next;
}

int
iterator_next_internal(struct iterator *it, struct tuple **ret)
{
	assert(it->next_internal != NULL);
	return it->next_internal(it, ret);
}

struct index *
index_new()
{
	struct index *index = (struct index *)malloc(sizeof(struct index));
	if (index == NULL) {
		fprintf(stderr, "Failed to allocate %u bytes in %s for %s\n", sizeof(struct index), "malloc", "struct memtx_space");
		return NULL;
	}
	static uint32_t unique_id = 0;
	index->unique_id = unique_id++;
	/* Unusable until set to proper value during space creation. */
	index->dense_id = UINT32_MAX;
	rlist_create(&index->read_gaps);
	new (&index->tree) std::map<int, struct tuple *>();
	return index;
}
