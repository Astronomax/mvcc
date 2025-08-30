#include "memtx_space.h"
#include "assert.h"

int
memtx_space_get(struct memtx_space *space, int key, struct tuple **result)
{
	assert(space->index_count > 0);
	struct index *pk = space->index[0];
	return index_get(pk, key, result);
}

int
memtx_space_replace/*_all_keys*/(struct memtx_space *space, struct tuple *old_tuple, struct tuple *new_tuple, enum dup_replace_mode mode, struct tuple **result)
{
	assert(space->index_count > 0);
	struct index *pk = space->index[0];
	/* Для простоты у нас все индексы будут уникальными. */
	//assert(pk->def->opts.is_unique);

	/* Реплейсы должны происходить внутри транзакции. */
	assert(/*space->def->opts.is_ephemeral ||*/
	       (in_txn() != NULL && txn_current_stmt(in_txn()) != NULL));
	/* ephemeral поддерживать не будем. */
	//if (memtx_tx_manager_use_mvcc_engine && !space->def->opts.is_ephemeral) {
		struct txn_stmt *stmt = txn_current_stmt(in_txn());
		return memtx_tx_history_add_stmt(stmt, old_tuple, new_tuple, mode, result);
	//}
}

static inline int
memtx_space_replace_tuple(struct memtx_space *space, struct txn_stmt *stmt, struct tuple *old_tuple, struct tuple *new_tuple, enum dup_replace_mode mode)
{
	struct memtx_space *memtx_space = (struct memtx_space *)space;
	struct tuple *result;
	int rc = memtx_space_replace(space, old_tuple, new_tuple, mode, &result);
	if (rc != 0)
		return rc;
	txn_stmt_prepare_rollback_info(stmt, result, new_tuple);
	stmt->new_tuple = new_tuple;
	stmt->old_tuple = result;
	return 0;
}

int
memtx_space_execute_replace(struct memtx_space *space, struct txn *txn, struct tuple *new_tuple, enum dup_replace_mode mode, struct tuple **result)
{
	struct txn_stmt *stmt = txn_current_stmt(txn);
	if (new_tuple == NULL) {
		return -1;
	}
	if (memtx_space_replace_tuple(space, stmt, NULL, new_tuple, mode) != 0)
		return -1;
	*result = stmt->new_tuple;
	return 0;
}

int
memtx_space_execute_delete(struct memtx_space *space, struct txn *txn, uint32_t index_id, int key, struct tuple **result)
{
	struct txn_stmt *stmt = txn_current_stmt(txn);
	/* Try to find the tuple by unique key. */
	assert(index_id < space->index_count);
	struct index *pk = space->index[index_id];
	if (pk == NULL)
		return -1;
	struct tuple *old_tuple;
	if (index_get_internal(pk, key, &old_tuple) != 0)
		return -1;
	if (old_tuple == NULL) {
		*result = NULL;
		return 0;
	}
	if (memtx_space_replace_tuple(space, stmt, old_tuple, NULL, DUP_REPLACE_OR_INSERT) != 0)
		return -1;
	*result = stmt->old_tuple;
	return 0;
}

int
memtx_space_create_index(struct memtx_space *space)
{
	if (space->index_count > BOX_INDEX_MAX)
		return -1;

	int dense_id = space->index_count++;
	space->index[dense_id] = index_new();
	space->index[dense_id]->space = space;
	space->index[dense_id]->_key_def = dense_id;
	space->index[dense_id]->dense_id = dense_id;
	space->index[dense_id]->built = false;

	if (memtx_space_build_index(space, space->index[dense_id]) != 0) {
		--space->index_count;
		//index_free(space->index[dense_id]);
		space->index[dense_id] = NULL;
		return -1;
	}
	space->index[dense_id]->built = true;
	return 0;
}

struct memtx_space *
memtx_space_new(uint32_t index_count)
{
	struct memtx_space *memtx_space = malloc(sizeof(struct memtx_space));
	if (memtx_space == NULL) {
		fprintf(stderr, "Failed to allocate %u bytes in %s for %s\n", sizeof(struct memtx_space), "malloc", "struct memtx_space");
		return NULL;
	}
	static uint32_t space_id = 0;
	memtx_space->id = space_id++;
	for (int i = 0; i < index_count; i++) {
		memtx_space->index[i] = index_new();
		memtx_space->index[i]->space = memtx_space;
		memtx_space->index[i]->_key_def = i;
		memtx_space->index[i]->dense_id = i;
		memtx_space->index[i]->built = true;
	}
	memtx_space->index_count = index_count;
	return memtx_space;
}
