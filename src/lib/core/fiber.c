/*
 * Copyright 2010-2016, Tarantool AUTHORS, please see AUTHORS file.
 *
 * Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following
 * conditions are met:
 *
 * 1. Redistributions of source code must retain the above
 *    copyright notice, this list of conditions and the
 *    following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials
 *    provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY <COPYRIGHT HOLDER> ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * <COPYRIGHT HOLDER> OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
#include "fiber.h"

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pmatomic.h>
#include "memory.h"
#include <trivia/util.h>

#include <valgrind/memcheck.h>

static int (*fiber_invoke)(fiber_func f, va_list ap);

#if ENABLE_ASAN
#include <sanitizer/asan_interface.h>

#define ASAN_START_SWITCH_FIBER(fake_stack_save, will_switch_back, bottom,     \
				size)					       \
	/*								       \
	 * When leaving a fiber definitely, NULL must be passed as the first   \
	 * argument so that the fake stack is destroyed.		       \
	 */								       \
	void *fake_stack_save = NULL;					       \
	__sanitizer_start_switch_fiber((will_switch_back) ? &fake_stack_save   \
							  : NULL,	       \
                                       (bottom), (size))
#if ASAN_INTERFACE_OLD
#define ASAN_FINISH_SWITCH_FIBER(fake_stack_save) \
	__sanitizer_finish_switch_fiber(fake_stack_save)
#else
#define ASAN_FINISH_SWITCH_FIBER(fake_stack_save) \
	__sanitizer_finish_switch_fiber(fake_stack_save, NULL, NULL)
#endif

#else
#define ASAN_START_SWITCH_FIBER(fake_stack_save, will_switch_back, bottom, size)
#define ASAN_FINISH_SWITCH_FIBER(fake_stack_save)
#endif

static inline int
fiber_madvise(void *addr, size_t len, int advice)
{
	if (madvise(addr, len, advice) != 0) {
		fprintf(stderr, "fiber madvise failed");
		return -1;
	}
	return 0;
}

static inline int
fiber_mprotect(void *addr, size_t len, int prot)
{
/*
 * If we panic then fiber stacks remain protected which cause leak sanitizer
 * failures. Disable memory protection under ASAN.
 */
#ifndef ENABLE_ASAN
	if (mprotect(addr, len, prot) != 0) {
		fprintf(stderr, "fiber mprotect failed");
		return -1;
	}
#endif
	return 0;
}

__thread struct cord *cord_ptr = NULL;

static size_t page_size;
static int stack_direction;

#ifndef FIBER_STACK_SIZE_DEFAULT
#error "Default fiber stack size is not set"
#endif

enum {
    /* The minimum allowable fiber stack size in bytes */
    FIBER_STACK_SIZE_MINIMAL = 16384,
	/* Stack size watermark in bytes. */
	FIBER_STACK_SIZE_WATERMARK = 65536,
};

#ifdef HAVE_MADV_DONTNEED
/*
 * Random values generated with uuid.
 * Used for stack poisoning.
 */
static const uint64_t poison_pool[] = {
	0x74f31d37285c4c37, 0xb10269a05bf10c29,
	0x0994d845bd284e0f, 0x9ffd4f7129c184df,
	0x357151e6711c4415, 0x8c5e5f41aafe6f28,
	0x6917dd79e78049d5, 0xba61957c65ca2465,
};

/*
 * We poison by 8 bytes as it's natural for stack
 * step on x86-64. Also 128 byte gap between poison
 * values should cover common cases.
 */
#define POISON_SIZE	(sizeof(poison_pool) / sizeof(poison_pool[0]))
#define POISON_OFF	(128 / sizeof(poison_pool[0]))

#endif /* HAVE_MADV_DONTNEED */

/** Default fiber attributes */
static const struct fiber_attr fiber_attr_default = {
	.stack_size = FIBER_STACK_SIZE_DEFAULT
};

void
fiber_attr_create(struct fiber_attr *fiber_attr)
{
	*fiber_attr = fiber_attr_default;
}

struct fiber_attr *
fiber_attr_new(void)
{
	struct fiber_attr *fiber_attr = malloc(sizeof(*fiber_attr));
	if (fiber_attr == NULL)  {
		fprintf(stderr, "Failed to allocate %u bytes in %s for %s\n", sizeof(*fiber_attr), "runtime", "fiber attr");
		return NULL;
	}
	fiber_attr_create(fiber_attr);
	return fiber_attr;
}

void
fiber_attr_delete(struct fiber_attr *fiber_attr)
{
	free(fiber_attr);
}

int
fiber_attr_setstacksize(struct fiber_attr *fiber_attr, size_t stack_size)
{
	if (stack_size < FIBER_STACK_SIZE_MINIMAL) {
		errno = EINVAL;
		fprintf(stderr, "stack size is too small");
		return -1;
	}
	fiber_attr->stack_size = stack_size;
	if (stack_size != FIBER_STACK_SIZE_DEFAULT) {
		fiber_attr->flags |= FIBER_CUSTOM_STACK;
	} else {
		fiber_attr->flags &= ~FIBER_CUSTOM_STACK;
	}
	return 0;
}

size_t
fiber_attr_getstacksize(struct fiber_attr *fiber_attr)
{
	return fiber_attr != NULL ? fiber_attr->stack_size :
	       fiber_attr_default.stack_size;
}

static void
fiber_recycle(struct fiber *fiber);

static void
fiber_stack_recycle(struct fiber *fiber);

/**
 * Try to delete a fiber right now or later if can't do now. The latter happens
 * for self fiber - can't delete own stack.
 */
static void
cord_add_garbage(struct cord *cord, struct fiber *f);

/**
 * True if a fiber with `fiber_flags` can be reused.
 * A fiber can not be reused if it is somehow non-standard.
 */
static bool
fiber_is_reusable(uint32_t fiber_flags)
{
	/* For now we can not reuse fibers with custom stack size. */
	return (fiber_flags & FIBER_CUSTOM_STACK) == 0;
}

/**
 * Transfer control to callee fiber.
 */
static void
fiber_call_impl(struct fiber *callee)
{
	struct fiber *caller = fiber();
	struct cord *cord = cord();

	/* Ensure we aren't switching to a fiber parked in fiber_loop */
	assert(callee->flags & FIBER_IS_READY || callee == &cord->sched);
	assert(! (callee->flags & FIBER_IS_DEAD));
	/*
	 * Ensure the callee was removed from cord->ready list.
	 * If it wasn't, the callee will observe a 'spurious' wakeup
	 * later, due to a fiber_wakeup() performed in the past.
	 */
	assert(rlist_empty(&callee->state));
	assert(caller);
	assert(caller != callee);
	assert((caller->flags & FIBER_IS_RUNNING) != 0);
	assert((callee->flags & FIBER_IS_RUNNING) == 0);

	caller->flags &= ~FIBER_IS_RUNNING;
	cord->fiber = callee;
	callee->flags = (callee->flags & ~FIBER_IS_READY) | FIBER_IS_RUNNING;

	ASAN_START_SWITCH_FIBER(asan_state, 1,
				callee->stack,
				callee->stack_size);
	coro_transfer(&caller->ctx, &callee->ctx);
	ASAN_FINISH_SWITCH_FIBER(asan_state);
}

void
fiber_call(struct fiber *callee)
{
	struct fiber *caller = fiber();
	assert(! (caller->flags & FIBER_IS_READY));
	assert(rlist_empty(&callee->state));
	assert(! (callee->flags & FIBER_IS_READY));

	callee->caller = caller;
	callee->flags |= FIBER_IS_READY;
	caller->flags |= FIBER_IS_READY;
	fiber_call_impl(callee);
}

void
fiber_start(struct fiber *callee, ...)
{
	va_start(callee->f_data, callee);
	fiber_call(callee);
	va_end(callee->f_data);
}

static void
fiber_make_ready(struct fiber *f)
{
	/**
	 * Do nothing if the fiber is already in cord->ready
	 * list *or* is in the call chain created by
	 * fiber_schedule_list(). While it's harmless to re-add
	 * a fiber to cord->ready, even if it's already there,
	 * but the same game is deadly when the fiber is in
	 * the callee list created by fiber_schedule_list().
	 *
	 * To put it another way, fiber_make_ready() is a 'request' to
	 * schedule the fiber for execution, and once it is executing
	 * the 'make ready' request is considered complete and it must be
	 * removed.
	 */
	assert((f->flags & (FIBER_IS_DEAD | FIBER_IS_READY)) == 0);
	struct cord *cord = cord();
	if (rlist_empty(&cord->ready)) {
		/*
		 * ev_feed_event(EV_CUSTOM) gets scheduled in the
		 * same event loop iteration, and we rely on this
		 * for quick scheduling. For a wakeup which
		 * actually can invoke a poll() in libev,
		 * use fiber_sleep(0)
		 */
		ev_feed_event(cord->loop, &cord->wakeup_event, EV_CUSTOM);
	}
	/**
	 * Removes the fiber from whatever wait list it is on.
	 *
	 * It's critical that the newly scheduled fiber is
	 * added to the tail of the list, to preserve correct
	 * transaction commit order after a successful WAL write.
	 * (see tx_schedule_queue() in box/wal.c)
	 */
	rlist_move_tail_entry(&cord->ready, f, state);
	f->flags |= FIBER_IS_READY;
}

void
fiber_set_ctx(struct fiber *f, void *f_arg)
{
	if (f == NULL)
		f = fiber();
	f->f_arg = f_arg;
}

void *
fiber_get_ctx(struct fiber *f)
{
	if (f == NULL)
		f = fiber();
	return f->f_arg;
}

void
fiber_wakeup(struct fiber *f)
{
	/*
	 * DEAD fiber can be lingering in the cord fiber list
	 * if it is joinable. And once its execution is complete
	 * it should be reaped with fiber_join() call.
	 *
	 * Still our API allows to call fiber_wakeup() on dead
	 * joinable fibers so simply ignore it.
	 */
	assert((f->flags & FIBER_IS_DEAD) == 0 ||
	       (f->flags & FIBER_IS_JOINABLE) != 0);
	const int no_flags = FIBER_IS_READY | FIBER_IS_DEAD | FIBER_IS_RUNNING;
	
	if ((f->flags & FIBER_IS_READY) != 0) {
		fprintf(stdout, "FIBER_IS_READY\n");
		fflush(stdout);
	}
	
	if ((f->flags & no_flags) == 0)
		fiber_make_ready(f);
}

void
fiber_cancel(struct fiber *f)
{
	if (fiber_is_dead(f)) {
		fprintf(stderr, "Cancel of a finished and already "
			  "recycled fiber");
		exit(1);
	}

	f->flags |= FIBER_IS_CANCELLED;
	fiber_wakeup(f);
}

bool
fiber_is_cancelled(void)
{
	return fiber()->flags & FIBER_IS_CANCELLED;
}

void
fiber_set_joinable(struct fiber *fiber, bool yesno)
{
	if (fiber == NULL)
		fiber = fiber();

	/*
	 * The C fiber API does not allow to report any error to the caller. At
	 * the same time using the function in some conditions is unsafe. So in
	 * case if such a condition is met the function panics.
	 *
	 * Here're the conditions the function may be called in:
	 * 1. The fiber is not joinable and hasn't finished yet. We're good to
	 *    change the fiber's joinability.
	 * 2. The fiber is not joinable and is finished. That means the fiber
	 *    is recycled already, so this is a use after free. This case is
	 *    impossible from the Lua world, but can be done with C API, so it
	 *    is to be prohibited.
	 * 3. The fiber is joinable, not finished and not joined. We're good to
	 *    change its joinability.
	 * 4. The fiber is joinable, not finished, but joined already. Making
	 *    the fiber non-joinable will lead to a double free: one in the
	 *    fiber_loop, the second one in the active fiber_join_timeout.
	 *    Making it joinable is a sign of attempt to join it later, so we
	 *    can expect the second join in the future - detect it now, while
	 *    we can do it, because in the future the fiber struct may be
	 *    reused and it will be much more difficult to find the root cause
	 *    of the double join (or we won't be able to detect it at all).
	 * 5. The fiber is joinable, finished and not joined. The fiber should
	 *    be joined in order to be recycled, so making it non-joinable can
	 *    lead to a fiber leak and to be prohibited. The point about making
	 *    it joinable from the statement #4 is applied here too.
	 * 6. The fiber is joinable, finished and joined. In order to avoid
	 *    introducing a new fiber flag, a joined fiber becomes non-joinable
	 *    on death (see the fiber_join_timeout implementation), so this
	 *    condition transforms into #2. And it's a use after free too.
	 *
	 * Simplifying:
	 *   OK:
	 *     1: !is_joinable && !is_dead
	 *     3: is_joinable && !is_dead && !is_joined
	 *   NOT OK:
	 *     2: !is_joinable && is_dead
	 *     4: is_joinable && !is_dead && is_joined
	 *     5: is_joinable && is_dead && !is_joined
	 *     6. is_joinable && is_dead && is_joined
	 *
	 *  Othervice, OK: !is_dead && (!is_joinable || !is_joined)
	 *  So NOT OK: is_dead || (is_joinable && is_joined)
	 *  So NOT OK: is_dead || is_joined, because joined implies joinable.
	 */
	if ((fiber->flags & FIBER_IS_DEAD) != 0 ||
	    (fiber->flags & FIBER_JOIN_BEEN_INVOKED) != 0) {
		fprintf(stderr, "%s on a dead or joined fiber detected", __func__);
		exit(1);
	}

	if (yesno == true)
		fiber->flags |= FIBER_IS_JOINABLE;
	else
		fiber->flags &= ~FIBER_IS_JOINABLE;
}

double
fiber_clock(void)
{
	return ev_monotonic_now(loop());
}

/**
 * Move current fiber to the end of ready fibers list and switch to next
 */
void
fiber_reschedule(void)
{
	struct fiber *f = fiber();
	/*
	 * The current fiber can't be dead, the flag is set when the fiber
	 * function returns. Can't be ready, because such status is assigned
	 * only to the queued fibers in the ready-list.
	 */
	assert((f->flags & (FIBER_IS_READY | FIBER_IS_DEAD)) == 0);
	fiber_make_ready(f);
	fiber_yield();
}

int
fiber_join(struct fiber *fiber)
{
	return fiber_join_timeout(fiber, TIMEOUT_INFINITY);
}

bool
fiber_wait_on_deadline(struct fiber *fiber, double deadline)
{
	rlist_add_tail_entry(&fiber->wake, fiber(), state);

	return fiber_yield_deadline(deadline);
}

int
fiber_join_timeout(struct fiber *fiber, double timeout)
{
	if ((fiber->flags & FIBER_IS_JOINABLE) == 0) {
		fprintf(stderr, "the fiber is not joinable");
		exit(1);
	}

	if ((fiber->flags & FIBER_JOIN_BEEN_INVOKED) != 0) {
		fprintf(stderr, "join of a joined fiber detected");
		exit(1);
	}

	if (fiber() == fiber) {
		fprintf(stderr, "cannot join itself");
		exit(1);
	}

	/* Prohibit joining the fiber and changing its joinability. */
	fiber->flags |= FIBER_JOIN_BEEN_INVOKED;

	if (!fiber_is_dead(fiber)) {
		double deadline = fiber_clock() + timeout;
		while (!fiber_wait_on_deadline(fiber, deadline) &&
		       !fiber_is_dead(fiber)) {
		}
		if (!fiber_is_dead(fiber)) {
			/*
			 * Not exactly the right error message for this place.
			 * Error message is generated based on the ETIMEDOUT
			 * code, that is used for network timeouts in linux. But
			 * in other places, this type of error is always used
			 * when the timeout expires, regardless of whether it is
			 * related to the network (see cbus_call for example).
			 */
			fprintf(stderr, "timed out");
			return -1;
		}
	}
	assert((fiber->flags & FIBER_IS_RUNNING) == 0);
	assert((fiber->flags & FIBER_IS_JOINABLE) != 0);
	/*
	 * This line is here just to make the following statement true: if
	 * a fiber is dead and is not joinable, that means it's recycled.
	 * So we don't have to introduce a new FIBER_IS_RECYCLED flag.
	 */
	fiber->flags &= ~FIBER_IS_JOINABLE;

	int ret = fiber->f_ret;
	/* The fiber is already dead. */
	fiber_recycle(fiber);
	return ret;
}

/**
 * Implementation of `fiber_yield()` and `fiber_yield_final()`.
 * `will_switch_back` argument is used only by ASAN.
 */
static void
fiber_yield_impl(MAYBE_UNUSED bool will_switch_back)
{
	struct cord *cord = cord();
	struct fiber *caller = cord->fiber;
	struct fiber *callee = caller->caller;
	caller->caller = &cord->sched;

	assert(callee->flags & FIBER_IS_READY || callee == &cord->sched);
	assert(! (callee->flags & FIBER_IS_DEAD));
	assert((caller->flags & FIBER_IS_RUNNING) != 0);
	assert((callee->flags & FIBER_IS_RUNNING) == 0);

	caller->flags &= ~FIBER_IS_RUNNING;
	cord->fiber = callee;
	callee->flags = (callee->flags & ~FIBER_IS_READY) | FIBER_IS_RUNNING;

	ASAN_START_SWITCH_FIBER(asan_state, will_switch_back, callee->stack,
				callee->stack_size);
	coro_transfer(&caller->ctx, &callee->ctx);
	ASAN_FINISH_SWITCH_FIBER(asan_state);
}

void
fiber_yield(void)
{
	fiber_yield_impl(true);
}

/**
 * Like `fiber_yield()`, but should be used when this is the last switch from
 * a dead fiber to the scheduler.
 */
static void
fiber_yield_final(void)
{
	fiber_yield_impl(false);
}


struct fiber_watcher_data {
	struct fiber *f;
	bool timed_out;
};

static void
fiber_schedule_timeout(ev_loop *loop,
		       ev_timer *watcher, int revents)
{
	(void) loop;
	(void) revents;

	assert(fiber() == &cord()->sched);
	struct fiber_watcher_data *state =
			(struct fiber_watcher_data *) watcher->data;
	state->timed_out = true;
	fiber_wakeup(state->f);
}

/**
 * @brief yield & check timeout
 * @return true if timeout exceeded
 */
bool
fiber_yield_timeout(ev_tstamp delay)
{
	struct ev_timer timer;
	ev_timer_init(&timer, fiber_schedule_timeout, delay, 0);
	struct fiber_watcher_data state = { fiber(), false };
	timer.data = &state;
	ev_timer_start(loop(), &timer);
	fiber_yield();
	ev_timer_stop(loop(), &timer);
	return state.timed_out;
}

bool
fiber_yield_deadline(ev_tstamp deadline)
{
	ev_tstamp timeout = deadline - ev_monotonic_now(loop());
	return fiber_yield_timeout(timeout);
}

/**
 * Yield the current fiber to events in the event loop.
 */
void
fiber_sleep(double delay)
{
	/*
	 * libev sleeps at least backend_mintime, which is 1 ms in
	 * case of poll()/Linux, unless there are idle watchers.
	 * So, to properly implement fiber_sleep(0), i.e. a sleep
	 * with a zero timeout, we set up an idle watcher, and
	 * it triggers libev to poll() with zero timeout.
	 */
	if (delay == 0) {
		ev_idle_start(loop(), &cord()->idle_event);
	}
	fiber_yield_timeout(delay);

	if (delay == 0) {
		ev_idle_stop(loop(), &cord()->idle_event);
	}
}

void
fiber_schedule_cb(ev_loop *loop, ev_watcher *watcher, int revents)
{
	(void) loop;
	(void) revents;
	struct fiber *fiber = watcher->data;
	assert(fiber() == &cord()->sched);
	fiber_wakeup(fiber);
}

static inline void
fiber_schedule_list(struct rlist *list)
{
	struct fiber *first;
	struct fiber *last;

	/*
	 * Happens when a fiber exits and is removed from cord->ready
	 * resulting in the empty list.
	 */
	if (rlist_empty(list))
		return;

	first = last = rlist_shift_entry(list, struct fiber, state);
	assert(last->flags & FIBER_IS_READY);

	while (! rlist_empty(list)) {
		last->caller = rlist_shift_entry(list, struct fiber, state);
		last = last->caller;
		assert(last->flags & FIBER_IS_READY);
	}
	last->caller = fiber();
	assert(fiber() == &cord()->sched);
	fiber_call_impl(first);
}

static void
fiber_schedule_wakeup(ev_loop *loop, ev_async *watcher, int revents)
{
	(void) loop;
	(void) watcher;
	(void) revents;
	struct cord *cord = cord();
	fiber_check_gc();
	fiber_schedule_list(&cord->ready);
}

static void
fiber_schedule_idle(ev_loop *loop, ev_idle *watcher,
		    int revents)
{
	(void) loop;
	(void) watcher;
	(void) revents;
}

void
fiber_gc(void)
{
	if (region_used(&fiber()->gc) < 128 * 1024) {
		region_reset(&fiber()->gc);
		return;
	}

	region_free(&fiber()->gc);
}

/** Destroy an active fiber and prepare it for reuse or delete it. */
static void
fiber_recycle(struct fiber *fiber)
{
	assert((fiber->flags & FIBER_IS_DEAD) != 0);
	/* no pending wakeup */
	assert(rlist_empty(&fiber->state));
	fiber_stack_recycle(fiber);
	fiber->f = NULL;
	fiber->gc_initial_size = 0;
	region_free(&fiber->gc);
	if (fiber_is_reusable(fiber->flags)) {
		rlist_move_entry(&cord()->dead, fiber, link);
	} else {
		cord_add_garbage(cord(), fiber);
	}
}

void
fiber_check_gc(void)
{
	struct fiber *fiber = fiber();

	assert(region_used(&fiber->gc) >= fiber->gc_initial_size);
	if (region_used(&fiber->gc) == fiber->gc_initial_size)
		return;

	fprintf(stderr, "Fiber gc leak is found. ");
	exit(1);
}

static void
fiber_loop(MAYBE_UNUSED void *data)
{
	ASAN_FINISH_SWITCH_FIBER(NULL);
	for (;;) {
		struct fiber *fiber = fiber();

		assert(fiber != NULL && fiber->f != NULL);
		fiber->f_ret = fiber_invoke(fiber->f, fiber->f_data);
		fiber_check_gc();
		fiber->flags |= FIBER_IS_DEAD;
		while (! rlist_empty(&fiber->wake)) {
			struct fiber *f;
			f = rlist_shift_entry(&fiber->wake, struct fiber, state);
			assert(f != fiber);
			fiber_wakeup(f);
		}
		/* reset pending wakeups */
		rlist_del(&fiber->state);
		if (! (fiber->flags & FIBER_IS_JOINABLE))
			fiber_recycle(fiber);
		/*
		 * Crash if spurious wakeup happens, don't call the old
		 * function again, ap is garbage by now.
		 */
		fiber->f = NULL;
		/*
		 * Give control back to the scheduler.
		 * If the fiber is not reusable, this is its final yield.
		 */
		if (fiber_is_reusable(fiber->flags))
			fiber_yield();
		else
			fiber_yield_final();
	}
}

static inline void *
page_align_down(void *ptr)
{
	return (void *)((intptr_t)ptr & ~(page_size - 1));
}

static inline void *
page_align_up(void *ptr)
{
	return page_align_down(ptr + page_size - 1);
}

/**
 * Call madvise(2) on given range but align start on page up and
 * end on page down.
 *
 * This way madvise(2) requirement on alignment of start address is met.
 * Also we won't touch memory after end due to rounding up of range length.
 */
static inline int
fiber_madvise_unaligned(void *start, void *end, int advice)
{
	start = page_align_up(start);
	end = page_align_down(end);
	return fiber_madvise(start, (char *)end - (char *)start, advice);
}

#ifdef HAVE_MADV_DONTNEED
/**
 * Check if stack poison values are present starting from
 * the address provided.
 */
static bool
stack_has_watermark(void *addr)
{
	const uint64_t *src = poison_pool;
	const uint64_t *dst = addr;
	size_t i;

	for (i = 0; i < POISON_SIZE; i++) {
		if (*dst != src[i])
			return false;
		dst += POISON_OFF;
	}
	return true;
}

/**
 * Put stack poison values starting from the address provided.
 */
static void
stack_put_watermark(void *addr)
{
	const uint64_t *src = poison_pool;
	uint64_t *dst = addr;
	size_t i;

	for (i = 0; i < POISON_SIZE; i++) {
		*dst = src[i];
		dst += POISON_OFF;
	}
}

/**
 * Free stack memory above the watermark when a fiber is recycled.
 * To avoid a pointless syscall invocation in case the fiber hasn't
 * touched memory above the watermark, we only call madvise() if
 * the fiber has overwritten a poison value.
 */
static void
fiber_stack_recycle(struct fiber *fiber)
{
	if (fiber->stack_watermark == NULL ||
	    stack_has_watermark(fiber->stack_watermark))
		return;
	/*
	 * When dropping pages make sure the page containing
	 * the watermark isn't touched since we're updating
	 * it anyway.
	 */
	void *start, *end;
	if (stack_direction < 0) {
		start = fiber->stack;
		end = fiber->stack_watermark;
	} else {
		start = fiber->stack_watermark;
		end = fiber->stack + fiber->stack_size;
	}

	/*
	 * Ignore errors on MADV_DONTNEED because this is
	 * just a hint for OS and not critical for
	 * functionality.
	 */
	fiber_madvise_unaligned(start, end, MADV_DONTNEED);
	stack_put_watermark(fiber->stack_watermark);
}

/**
 * Initialize fiber stack watermark.
 */
static void
fiber_stack_watermark_create(struct fiber *fiber,
			     const struct fiber_attr *fiber_attr)
{
	assert(fiber->stack_watermark == NULL);

	/* No tracking on custom stacks for simplicity. */
	if (fiber_attr->flags & FIBER_CUSTOM_STACK)
		return;

	/*
	 * We don't expect the whole stack usage in regular
	 * loads, let's try to minimize rss pressure. But do
	 * not exit if MADV_DONTNEED failed, it is just a hint
	 * for OS, not critical one.
	 */
	fiber_madvise_unaligned(fiber->stack, fiber->stack + fiber->stack_size,
				MADV_DONTNEED);
	/*
	 * To increase probability of stack overflow detection
	 * we put the first mark at a random position.
	 */
	size_t offset = rand() % POISON_OFF * sizeof(poison_pool[0]);
	if (stack_direction < 0) {
		fiber->stack_watermark  = fiber->stack + fiber->stack_size;
		fiber->stack_watermark -= FIBER_STACK_SIZE_WATERMARK;
		fiber->stack_watermark += offset;
	} else {
		fiber->stack_watermark  = fiber->stack;
		fiber->stack_watermark += FIBER_STACK_SIZE_WATERMARK;
		fiber->stack_watermark -= page_size;
		fiber->stack_watermark += offset;
	}
	stack_put_watermark(fiber->stack_watermark);
}
#else
static void
fiber_stack_recycle(struct fiber *fiber)
{
	(void)fiber;
}

static void
fiber_stack_watermark_create(struct fiber *fiber,
			     const struct fiber_attr *fiber_attr)
{
	(void)fiber;
	(void)fiber_attr;
}
#endif /* HAVE_MADV_DONTNEED */

static void
fiber_stack_destroy(struct fiber *fiber, struct slab_cache *slabc)
{
	static const int mprotect_flags = PROT_READ | PROT_WRITE;

	if (fiber->stack != NULL) {
		VALGRIND_STACK_DEREGISTER(fiber->stack_id);
		void *guard;
		if (stack_direction < 0)
			guard = page_align_down(fiber->stack - page_size);
		else
			guard = page_align_up(fiber->stack + fiber->stack_size);

		if (fiber_mprotect(guard, page_size, mprotect_flags) != 0) {
			/*
			 * FIXME: We need some intelligent handling:
			 * say put this slab into a queue and retry
			 * to setup the original protection back in
			 * background.
			 *
			 * For now lets keep such slab referenced and
			 * leaked: if mprotect failed we must not allow
			 * to reuse such slab with PROT_NONE'ed page
			 * inside.
			 *
			 * Note that in case if we're called from
			 * fiber_stack_create() the @a mprotect_flags is
			 * the same as the slab been created with, so
			 * calling mprotect for VMA with same flags
			 * won't fail.
			 */
			fprintf(stderr, "fiber: Can't put guard page to slab. "
				     "Leak %zu bytes", (size_t)fiber->stack_size);
		} else {
			slab_put(slabc, fiber->stack_slab);
		}
	}
}

static int
fiber_stack_create(struct fiber *fiber, const struct fiber_attr *fiber_attr,
		   struct slab_cache *slabc)
{
	size_t stack_size = fiber_attr->stack_size - slab_sizeof();
	fiber->stack_slab = slab_get(slabc, stack_size);

	if (fiber->stack_slab == NULL) {
		fprintf(stderr, "Failed to allocate %u bytes in %s for %s\n", stack_size, "runtime arena", "fiber stack");
		return -1;
	}
	void *guard;
	/* Adjust begin and size for stack memory chunk. */
	if (stack_direction < 0) {
		/*
		 * A stack grows down. First page after begin of a
		 * stack memory chunk should be protected and memory
		 * after protected page until end of memory chunk can be
		 * used for coro stack usage.
		 */
		guard = page_align_up(slab_data(fiber->stack_slab));
		fiber->stack = guard + page_size;
		fiber->stack_size = slab_data(fiber->stack_slab) + stack_size -
				    fiber->stack;
	} else {
		/*
		 * A stack grows up. Last page should be protected and
		 * memory from begin of chunk until protected page can
		 * be used for coro stack usage
		 */
		guard = page_align_down(fiber->stack_slab + stack_size) -
			page_size;
		fiber->stack = fiber->stack_slab + slab_sizeof();
		fiber->stack_size = guard - fiber->stack;
	}

	fiber->stack_id = VALGRIND_STACK_REGISTER(fiber->stack,
						  (char *)fiber->stack +
						  fiber->stack_size);

	if (fiber_mprotect(guard, page_size, PROT_NONE)) {
		fiber_stack_destroy(fiber, slabc);
		return -1;
	}
	return 0;
}

static void
fiber_gc_checker_init(struct fiber *fiber)
{
	fiber->gc_initial_size = 0;
}

struct fiber *
fiber_new_ex(const struct fiber_attr *fiber_attr, fiber_func f)
{
	struct cord *cord = cord();
	struct fiber *fiber = NULL;
	assert(fiber_attr != NULL);
	cord_collect_garbage(cord);

	if (fiber_is_reusable(fiber_attr->flags) && !rlist_empty(&cord->dead)) {
		fiber = rlist_first_entry(&cord->dead, struct fiber, link);
		rlist_move_entry(&cord->alive, fiber, link);
		assert(fiber_is_dead(fiber));
	} else {
		fiber = (struct fiber *)
			mempool_alloc(&cord->fiber_mempool);
		if (fiber == NULL) {
			fprintf(stderr, "Failed to allocate %u bytes in %s for %s\n", sizeof(struct fiber), "fiber pool", "fiber");
			return NULL;
		}
		memset(fiber, 0, sizeof(struct fiber));

		if (fiber_stack_create(fiber, fiber_attr, &cord()->slabc)) {
			mempool_free(&cord->fiber_mempool, fiber);
			return NULL;
		}
		coro_create(&fiber->ctx, fiber_loop, NULL,
			    fiber->stack, fiber->stack_size);

		region_create(&fiber->gc, &cord->slabc);

		rlist_create(&fiber->state);
		rlist_create(&fiber->wake);

		rlist_add_entry(&cord->alive, fiber, link);
	}
	fiber->flags = fiber_attr->flags;
	fiber->f = f;
	fiber_gc_checker_init(fiber);

	return fiber;
}

/**
 * Create a new fiber.
 *
 * Takes a fiber from fiber cache, if it's not empty.
 * Can fail only if there is not enough memory for
 * the fiber structure or fiber stack.
 *
 * The created fiber automatically returns itself
 * to the fiber cache when its "main" function
 * completes.
 */
struct fiber *
fiber_new(fiber_func f)
{
	return fiber_new_ex(&fiber_attr_default, f);
}

/** Free all fiber's resources. */
static void
fiber_destroy(struct cord *cord, struct fiber *f)
{
	assert(f != cord->fiber);
	rlist_del(&f->link);
	region_destroy(&f->gc);
	fiber_stack_destroy(f, &cord->slabc);
	TRASH(f);
}

void
fiber_delete(struct cord *cord, struct fiber *f)
{
	assert(f != &cord->sched);
	fiber_destroy(cord, f);
	mempool_free(&cord->fiber_mempool, f);
}

/** Delete all fibers in the given list so it becomes empty. */
static void
cord_delete_fibers_in_list(struct cord *cord, struct rlist *list)
{
	while (!rlist_empty(list)) {
		struct fiber *f = rlist_first_entry(list, struct fiber, link);
		fiber_delete(cord, f);
	}
}

void
fiber_delete_all(struct cord *cord)
{
	cord_collect_garbage(cord);
	cord_delete_fibers_in_list(cord, &cord->alive);
	cord_delete_fibers_in_list(cord, &cord->dead);
}

void
cord_create(struct cord *cord)
{
	cord_ptr = cord;
	slab_cache_set_thread(&cord()->slabc);

	cord->id = pthread_self();
	slab_cache_create(&cord->slabc, &runtime);
	mempool_create(&cord->fiber_mempool, &cord->slabc,
		       sizeof(struct fiber));
	rlist_create(&cord->alive);
	rlist_create(&cord->ready);
	rlist_create(&cord->dead);

	/* sched fiber is not present in alive/ready/dead list. */
	rlist_create(&cord->sched.state);
	rlist_create(&cord->sched.link);
	rlist_create(&cord->sched.wake);
	region_create(&cord->sched.gc, &cord->slabc);
	fiber_gc_checker_init(&cord->sched);
	cord->fiber = &cord->sched;
	cord->sched.flags = FIBER_IS_RUNNING;

	/*
	 * No need to start this event since it's only used for
	 * ev_feed_event(). Saves a few cycles on every
	 * event loop iteration.
	 */
	ev_async_init(&cord->wakeup_event, fiber_schedule_wakeup);

	ev_idle_init(&cord->idle_event, fiber_schedule_idle);

#if ENABLE_ASAN
	/* Record stack extents */
	tt_pthread_attr_getstack(cord->id, &cord->sched.stack,
				 &cord->sched.stack_size);
#else
	cord->sched.stack = NULL;
	cord->sched.stack_size = 0;
#endif
}

void
cord_collect_garbage(struct cord *cord)
{
	struct fiber *garbage = cord->garbage;
	if (garbage == NULL)
		return;
	fiber_delete(cord, garbage);
	cord->garbage = NULL;
}

static void
cord_add_garbage(struct cord *cord, struct fiber *f)
{
	cord_collect_garbage(cord);
	assert(cord->garbage == NULL);
	if (f != cord->fiber)
		fiber_delete(cord, f);
	else
		cord->garbage = f;
}

void
cord_destroy(struct cord *cord)
{
	assert(cord->id == 0 || pthread_equal(cord->id, pthread_self()));
	cord->id = 0;
	slab_cache_set_thread(&cord->slabc);
	fiber_delete_all(cord);
	cord->fiber = NULL;
	region_destroy(&cord->sched.gc);
	slab_cache_destroy(&cord->slabc);
}

static NOINLINE int
check_stack_direction(void *prev_stack_frame)
{
	return __builtin_frame_address(0) < prev_stack_frame ? -1: 1;
}

void
fiber_init(int (*invoke)(fiber_func f, va_list ap))
{
	page_size = small_getpagesize();
	stack_direction = check_stack_direction(__builtin_frame_address(0));
	fiber_invoke = invoke;
}