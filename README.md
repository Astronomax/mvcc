# transaction-manager

[![CI](https://github.com/Astronomax/transaction-manager/actions/workflows/ci.yml/badge.svg)](https://github.com/Astronomax/transaction-manager/actions/workflows/ci.yml)

This project provides a **simplified, heavily commented** implementation of [Tarantool](https://github.com/tarantool/tarantool)'s transaction manager (see `memtx_tx.c`) core functionality, designed for educational purposes. It demonstrates the fundamental transaction mechanics used in Tarantool while removing complex production features to focus on the essential concepts. If you want to understand how the Tarantool's transaction manager works, it is highly recommended to start with this repository. You can simply come up with some complex scenario and then run this project under the debugger or with debug prints.


The storage is simplified to the limit - `unordered_map` is used as indexes in the space. All indexes are unique.

A lot of the memory management stuff has been removed for simplicity, so there are quite a few potential leaks.

## Building and Running
```console
$ git submodule update --init --recursive #there is a submodule
$ mkdir build && cd build
$ cmake ..
$ make
$ ./memtx_tx
```

## Example Usage
```c
#include "core/fiber.h"
#include "core/memory.h"
#include "trivia/util.h"

#include "box.h"
#include "memtx_tx.h"
#include "tuple.h"

struct memtx_space *space;

int
f1_f(va_list ap)
{
    box_txn_begin();
    struct tuple *t = new tuple{.flags = 0, .data = {1, 1}};
    box_replace(space, t);
    fiber_sleep(0);
    box_txn_commit();
    return 0;
}

int
f2_f(va_list ap)
{
    box_txn_begin();
    struct tuple *t = new tuple{.flags = 0, .data = {2, 1}};
    box_replace(space, t);
    fiber_sleep(1);
    box_txn_commit();
    return 0;
}

int
main_f(va_list ap)
{
    space = memtx_space_new(2);
    struct fiber *f1 = fiber_new(f1_f);
    struct fiber *f2 = fiber_new(f2_f);
    fiber_set_joinable(f1, true);
    fiber_set_joinable(f2, true);
    fiber_wakeup(f1);
    fiber_wakeup(f2);
    fiber_join(f1);
    fiber_join(f2);

    box_txn_begin();
    struct tuple *res = NULL;
    box_get(space, 1, &res);
    fprintf(stderr, "get(1): %s\n", tuple_str(res));
    box_get(space, 2, &res);
    fprintf(stderr, "get(2): %s\n", tuple_str(res));
    box_txn_commit();

    return 0;
}

int main() {
    memory_init();
    fiber_init(fiber_c_invoke);
    memtx_tx_manager_init();

    cord()->loop = ev_loop_new(EVFLAG_AUTO | EVFLAG_ALLOCFD);
    if (cord()->loop == NULL) {
        fprintf(stderr, "Failed to allocate %u bytes in %s for %s\n", 0, "ev_loop_new", "ev_loop");
        memory_free();
    	return -1;
    }

    struct fiber *main_fiber = fiber_new(main_f);
    fiber_wakeup(main_fiber);
    ev_run(cord()->loop, 0);

    memory_free();
    return 0;
}
```

```console
Transaction has been aborted by conflict
get(1): {1, 1}
get(2): nil
```
