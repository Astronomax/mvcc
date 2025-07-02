set(core_sources
    memory.c
    fiber.c
    cord_on_demand.cc
)

add_library(core STATIC ${core_sources})

target_link_libraries(core small ${LIBEV_LIBRARIES} ${LIBCORO_LIBRARIES})
