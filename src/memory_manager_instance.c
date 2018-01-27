#include "memory_manager.h"

Manager manager;

u64 *instance_setup_manager(
        /* heap_size in u64s, arg_stack_size in entries */
        size_t heap_size, size_t arg_stack_size,
        u64 indirection, u64 iproc,
        u8 *stackmap) {
    return setup_manager(&manager, heap_size, arg_stack_size,
            indirection, iproc, stackmap);
}

u64 *instance_alloc_from(
        u8 *caller_entry, u64 *arg_stack,
        size_t count) {
    return alloc_from(&manager, caller_entry, arg_stack, count);
}

