#include "wal.h"

#include "fiber.h"

struct stailq wal_queue = STAILQ_INITIALIZER(wal_queue);

struct fiber *wal_worker;

/**
 * Initialize a new journal entry.
 */
static inline void
journal_entry_create(struct journal_entry *entry, journal_on_write_f on_write, void *complete_data)
{
	entry->on_write = on_write;
	entry->complete_data	= complete_data;
	entry->res		= JOURNAL_ENTRY_ERR_UNKNOWN;
	entry->is_complete = false;
	entry->fiber = NULL;
    entry->errinj_wal_io = false;
}

struct journal_entry *
journal_entry_new(journal_on_write_f on_write, void *complete_data)
{
	struct journal_entry *entry =
        (struct journal_entry *)malloc(sizeof(struct journal_entry));
	if (entry == NULL) {
        fprintf(stderr, "Failed to allocate %u bytes in %s for %s\n", sizeof(struct journal_entry), "malloc", "struct journal_entry");
		return NULL;
	}
	journal_entry_create(entry, on_write, complete_data);
	return entry;
}

void
journal_write_submit(struct journal_entry *entry)
{
    if (stailq_empty(&wal_queue))
        fiber_wakeup(wal_worker);

    stailq_add_tail_entry(&wal_queue, entry, fifo);
}

int
journal_write(struct journal_entry *entry)
{
    journal_write_submit(&entry);
    while (!entry->is_complete)
        fiber_yield();
    return 0;
}

/**
 * Complete asynchronous write.
 */
static inline void
journal_async_complete(struct journal_entry *entry)
{
	assert(entry->on_write != NULL);
	entry->is_complete = true;
	entry->on_write(entry);
}

/**
 * Invoke completion callbacks of journal entries to be
 * completed. Callbacks are invoked in strict fifo order:
 * this ensures that, in case of rollback, requests are
 * rolled back in strict reverse order, producing
 * a consistent database state.
 */
static void
tx_schedule_queue(struct stailq *queue)
{
	struct journal_entry *req, *tmp;
	stailq_foreach_entry_safe(req, tmp, queue, fifo)
		journal_async_complete(req);
}

static void
tx_complete_rollback(void)
{
	struct stailq rollback;
	stailq_create(&rollback);
	stailq_concat(&rollback, &wal_queue);
	stailq_reverse(&rollback);
	struct journal_entry *req;
	stailq_foreach_entry(req, &rollback, fifo) {
		req->res = JOURNAL_ENTRY_ERR_CASCADE;
		req->is_complete = true;
		req->on_write(req);
	}
}

static int
wal_worker_f(va_list args);

void
wal_init()
{
    wal_worker = fiber_new(wal_worker_f);
    if (wal_worker == NULL) {
        /*panic*/fprintf(stderr, "failed to allocate wal queue worker fiber\n");
        exit(1);
    }
    fiber_set_joinable(wal_worker, true);
}

static void
tx_complete_rollback(void);

static int
wal_worker_f(va_list args)
{
    (void)args;
    while (!fiber_is_cancelled()) {
        struct journal_entry *entry =
            stailq_first_entry(&wal_queue, struct journal_entry, fifo);
        //if (is_in_rollback) {
        //    fprintf(stderr, "WAL has a rollback in progress\n");
        //    fflush(stderr);
        //    entry->res = -1;
        //} else if (entry->errinj_wal_io) {
        //    fprintf(stderr, "Failed to write to disk\n");
        //    fflush(stderr);
        //    entry->res = -1;
        //
        //    if (!stailq_empty(&wal_queue))
        //        /* cascade rollback */
        //        is_in_rollback = true;
        //}
        if (entry->errinj_wal_io) {
            tx_complete_rollback();
        } else {
            stailq_shift(&wal_queue);
            //entry->res = vclock_sum(&vclock_diff) +
			//     vclock_sum(&writer->vclock);
            entry->res = 239;
            journal_async_complete(entry);
        }
        //fiber_wakeup(entry->fiber);

        if (!stailq_empty(&wal_queue))
            fiber_sleep(0);
        else
            fiber_yield();
    }
    return 0;
}