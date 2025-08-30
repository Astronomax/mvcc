#include "box.h"
#include "memtx_engine.h"
#include "memtx_engine.h"
#include "memtx_space.h"
#include "index.h"
#include "txn.h"

int
box_txn_begin(void)
{
	if (in_txn()) {
		fprintf(stderr, "Operation is not permitted when there is an active transaction\n");
		return -1;
	}
	if (txn_begin() == NULL)
		return -1;
	return 0;
}

int
box_txn_commit(void)
{
	struct txn *txn = in_txn();
	if (!txn)
		return 0;
	if (txn_check_can_complete(txn) != 0)
		return -1;
	return txn_commit(txn);
}

int
box_txn_rollback(void)
{
	struct txn *txn = in_txn();
	if (txn == NULL)
		return 0;
	if (txn_check_can_complete(txn) != 0)
		return -1;
	txn_rollback(txn); /* doesn't throw */
	return 0;
}

int
box_get(struct memtx_space *space, uint32_t index_id, int key, struct tuple **result)
{
	struct txn *txn = in_txn();
    if (txn == NULL)
        return -1;
	struct index *index = space->index[index_id];
	if (index == NULL || !index->built) {
		assert(false);
		fprintf(stderr, "Index not built\n");
		return -1;
	}
	if (txn_begin_ro_stmt(txn) != 0)
        return -1;
	if (index_get(index, key, result) != 0) {
		txn_rollback_stmt(txn);
		return -1;
	}
    return 0;
}

int
box_insert(struct memtx_space *space, struct tuple *new_tuple)
{
	struct tuple *unused = NULL;
	struct txn *txn = in_txn();
    if (txn == NULL)
        return -1;
	if (txn_begin_stmt(txn, space) != 0)
        return -1;
	if (memtx_space_execute_replace(space, txn, new_tuple, DUP_INSERT, &unused) != 0) {
		txn_rollback_stmt(txn);
		return -1;
	}
    return 0;
}

int
box_replace(struct memtx_space *space, struct tuple *new_tuple)
{
	struct tuple *unused = NULL;
	struct txn *txn = in_txn();
    if (txn == NULL)
        return -1;
	if (txn_begin_stmt(txn, space) != 0)
        return -1;
	if (memtx_space_execute_replace(space, txn, new_tuple, DUP_REPLACE_OR_INSERT, &unused) != 0) {
		txn_rollback_stmt(txn);
		return -1;
	}
    return 0;
}

int
box_delete(struct memtx_space *space, uint32_t index_id, int key, struct tuple **result)
{
	struct txn *txn = in_txn();
    if (txn == NULL)
        return -1;
	struct index *index = space->index[index_id];
	if (index == NULL || !index->built) {
		fprintf(stderr, "Index not built\n");
		return -1;
	}
	if (txn_begin_stmt(txn, space) != 0)
        return -1;
	if (memtx_space_execute_delete(space, txn, index_id, key, result) != 0) {
		txn_rollback_stmt(txn);
		return -1;
	}
    return 0;
}

int
box_space_build_index(struct memtx_space *space)
{
	if (box_txn_begin() != 0)
		return -1;
	uint32_t dense_id = space->index_count;
	if (memtx_space_create_index(space) != 0)
		return -1;
	if (box_txn_commit() != 0) {
		--space->index_count;
		//index_free(space->index[dense_id]);
		space->index[dense_id] = NULL;
		return -1;
	}
}