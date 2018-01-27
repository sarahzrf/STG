#include <stdint.h>
#include <stdlib.h>

typedef char     u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef  int32_t i32;

#define S8  sizeof(u8)
#define S16 sizeof(u16)
#define S32 sizeof(u32)
#define S64 sizeof(u64)

/* Pretty much all of this assumes that pointers are the same size as u64s.
 * Portability would be hard and I don't feel like it. */

typedef struct {
    u64 instruction, stack_size;
    u16 num_location_offsets;
    i32 *location_offsets;
} Statepoint;

typedef struct {
    /* start <= heap < end */
    /* start <= next <= end */
    u64 *start, *next, *end;
} Heap;

typedef struct {
    int in_progress;
    u8 *caller_entry;
    u64 *arg_stack;
} CollectionState;

typedef struct {
    CollectionState gc;

    /* We'll just swap the fields when we switch heaps. */
    Heap cur_heap, spare_heap;

    /* We'll need to be able to know when we're done walking the argstack. */
    u64 *arg_stack_start;

    /* First-field values that indicate special handling. */
    u64 indirection, iproc;

    size_t statepoint_count;
    Statepoint* statepoints;
} Manager;

u64 *setup_manager(Manager *manager,
        /* heap_size in u64s, arg_stack_size in entries */
        size_t heap_size, size_t arg_stack_size,
        u64 indirection, u64 iproc,
        u8 *stackmap);

u64 *alloc_from(
        Manager *manager,
        u8 *caller_entry, u64 *arg_stack,
        size_t count);

