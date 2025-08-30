#pragma once

#include "stdbool.h"
#include "stdint.h"

#include "salad/stailq.h"

#ifdef __cplusplus
extern "C" {
#endif

struct journal_entry;

typedef void
(*journal_on_write_f)(struct journal_entry *entry);

struct journal_entry 
{
	/** A helper to include requests into a FIFO queue. */
	struct stailq_entry fifo;
	/**
	 * On success, contains vclock signature of
	 * the committed transaction, on error is -1
	 */
	int64_t res;
	/**
	 * A journal entry completion callback argument.
	 */
	void *complete_data;
    /** Write completion function. */
	journal_on_write_f on_write;
	/**
	 * Set to true when execution of a batch that contains this
	 * journal entry is completed.
	 */
	bool is_complete;
	/**
	 * Fiber which put the request in journal queue.
	 */
	struct fiber *fiber;
    /* DEBUG */
    bool errinj_wal_io;
};

enum {
	/** Entry didn't attempt a journal write. */
	JOURNAL_ENTRY_ERR_UNKNOWN = -1,
	/** Tried to be written, but something happened related to IO. */
	JOURNAL_ENTRY_ERR_IO = -2,
	/**
	 * Rollback because there is a not finished rollback of a previous
	 * entry.
	 */
	JOURNAL_ENTRY_ERR_CASCADE = -3,
	/** Rollback due to fiber waiting for WAL is cancelled. */
	JOURNAL_ENTRY_ERR_CANCELLED = -4,
	/**
	 * Anchor for the structs built on top of journal entry so as they
	 * could introduce their own unique errors. Set to a big value in
	 * advance.
	 */
	JOURNAL_ENTRY_ERR_MIN = -100,
};

void
wal_init();

struct journal_entry *
journal_entry_new(journal_on_write_f on_write, void *complete_data);

void
journal_write_submit(struct journal_entry *entry);

int
journal_write(struct journal_entry *entry);

#ifdef __cplusplus
} // extern "C"
#endif
