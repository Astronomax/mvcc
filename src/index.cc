#include "index.h"
#include "memtx_tx.h"
#include "memtx_space.h"
#include "txn.h"
#include "stdbool.h"
#include <memory>

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
index_replace(struct index *index, struct tuple *old_tuple, struct tuple *new_tuple, enum dup_replace_mode mode, struct tuple **result/*, struct tuple **successor*/)
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
	new (&index->tree) std::unordered_map<int, struct tuple *>();
	return index;
}
