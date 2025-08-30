#pragma once

#include "index.h"
#include "tuple.h"
#include "txn.h"

#ifdef __cplusplus
extern "C" {
#endif

struct memtx_space {
	uint32_t id;
	uint32_t index_count;
	struct index *index[BOX_INDEX_MAX];
};

int
memtx_space_get(struct memtx_space *space, int key, struct tuple **result);

int
memtx_space_execute_replace(struct memtx_space *space, struct txn *txn, struct tuple *new_tuple, enum dup_replace_mode mode, struct tuple **result);

int
memtx_space_execute_delete(struct memtx_space *space, struct txn *txn, uint32_t index_id, int key, struct tuple **result);

int
memtx_space_create_index(struct memtx_space *space);

struct memtx_space *
memtx_space_new(uint32_t index_count);

#ifdef __cplusplus
} // extern "C"
#endif
