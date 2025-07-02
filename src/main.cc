#include "core/fiber.h"
#include "core/memory.h"
#include "trivia/util.h"

#include <iostream>

int
fiber_f(va_list ap)
{
    while (!fiber_is_cancelled()) {
        fprintf(stdout, "wake up!\n");
        fiber_sleep(3.0);
    }
    fprintf(stdout, "cancelled\n");
    return 0;
}

int
main(int argc, const char *argv[])
{
	memory_init();
	fiber_init(fiber_c_invoke);

    struct fiber *f = fiber_new(fiber_f);

    cord()->loop = ev_loop_new(EVFLAG_AUTO | EVFLAG_ALLOCFD);
	if (cord()->loop == NULL) {
		//TODO
        memory_free();
		return -1;
	}

    fiber_wakeup(f);

    ev_run(cord()->loop, 0);

	memory_free();
	return 0;
}
