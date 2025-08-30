#pragma once

#include "stdint.h"
#include "memtx_space.h"
#include "tuple.h"

#ifdef __cplusplus
extern "C" {
#endif

int
box_txn_begin(void);

int
box_txn_commit(void);

int
box_txn_rollback(void);

int
box_get(struct memtx_space *space, uint32_t index_id, int key, struct tuple **result);

int
box_insert(struct memtx_space *space, struct tuple *new_tuple);

int
box_replace(struct memtx_space *space, struct tuple *new_tuple);

int
box_delete(struct memtx_space *space, uint32_t index_id, int key, struct tuple **result);

int
box_space_build_index(struct memtx_space *space);

#ifdef __cplusplus
} // extern "C"
#endif
