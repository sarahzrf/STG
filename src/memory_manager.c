#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    uint64_t instruction, stack_size;
    uint8_t *stackmap_record;
} Statepoint;

typedef struct {
    /* heap_start <= heap < heap_end */
    /* We'll just swap the fields when we switch heaps. */
    void *cur_heap_start, *cur_heap_next, *cur_heap_end;
    void *spare_heap_start, *spare_heap_next, *spare_heap_end;

    /* We'll need to be able to recognize callstack gc roots that are
     * pointers into the argstack rather than pointers into the heap.
     * */
    void **arg_stack_start, **arg_stack_end;

    /* First-field values that indicate special handling. */
    void *indirection, *iproc;

    size_t statepoint_count;
    Statepoint* statepoints;
} Manager;

/* temporary var for testing purposes when we want a manager in our hand - for
 * some reason gdb's variables behave bizarrely */
Manager hand;

int compare_statepoints(const void *v1, const void *v2) {
    const Statepoint *s1 = v1, *s2 = v2;
    if (s1->instruction < s2->instruction) return -1;
    else if (s1->instruction == s2->instruction) return 0;
    else return 1;
}

#define S8  sizeof(uint8_t)
#define S16 sizeof(uint16_t)
#define S32 sizeof(uint32_t)
#define S64 sizeof(uint64_t)
/* https://llvm.org/docs/StackMaps.html#stackmap-format */
void parse_stackmap(Manager *manager, uint8_t *stackmap) {
    manager->statepoint_count = 0;
    Statepoint *next_statepoint = manager->statepoints =
        /* TODO don't hardcode this size */
        calloc(10000, sizeof(Statepoint));

    assert(*stackmap == 3);

    stackmap += S8 * 2 + S16; /* now at counts */
    uint32_t num_functions = ((uint32_t*)stackmap)[0],
             num_constants = ((uint32_t*)stackmap)[1],
             num_records   = ((uint32_t*)stackmap)[2];

    stackmap += S32 * 3; /* now at functions */
    uint8_t *cur_record = stackmap +
        S64 * 3 * num_functions + S64 * num_constants;

    for (uint32_t func_ix = 0; func_ix < num_functions; func_ix++) {
        uint64_t *func = (uint64_t*)stackmap;
        func += func_ix * 3;
        uint64_t addr = func[0], stack_size = func[1], record_count = func[2];

        for (; record_count > 0; record_count--) {
            assert(num_records > 0);
            num_records--;

            assert(*(uint64_t*)cur_record == 2882400000);
            uint32_t offset = *(uint32_t*)(cur_record + S64);
            Statepoint s = {addr + offset, stack_size, cur_record};
            manager->statepoint_count++;
            *next_statepoint = s;
            next_statepoint++;

            cur_record += S64 + S32 + S16; /* now at num_locations */
            uint16_t num_locations = *(uint16_t*)cur_record;
            cur_record += S16 +
                (S8 * 2 + S16 * 3 + S32) * (size_t)num_locations;
            if ((size_t)cur_record % 8 != 0) cur_record += S32;
            cur_record += S16; /* now at num_live_outs */
            uint16_t num_live_outs = *(uint16_t*)cur_record;
            cur_record += S16 + (S16 + S8 * 2) * (size_t)num_live_outs;
            if ((size_t)cur_record % 8 != 0) cur_record += S32;
        }
    }
    assert(num_records == 0);

    qsort(manager->statepoints,
            manager->statepoint_count, sizeof(Statepoint),
            compare_statepoints);
}

Statepoint *find_statepoint(Manager *manager, uint64_t instr) {
    Statepoint s;
    s.instruction = instr;
    return bsearch(&s, manager->statepoints, manager->statepoint_count,
            sizeof(Statepoint), compare_statepoints);
}

void crawl_stack(Manager *manager, uint8_t *stack_return) {
    for (;;) {
        uint64_t return_addr = *(uint64_t*)stack_return;
        printf("%p\n", return_addr);
        Statepoint *prev = find_statepoint(manager, return_addr);
        if (prev == NULL) break;
        stack_return += prev->stack_size + 8;
    }
}

void setup_manager(Manager *manager,
        /* heap_size in bytes, arg_stack_size in entries */
        size_t heap_size, size_t arg_stack_size,
        void *indirection, void *iproc,
        void *stackmap) {
    uint8_t *heap1 = calloc(heap_size, 1), *heap2 = calloc(heap_size, 1);
    manager->cur_heap_start   = manager->cur_heap_next   = heap1;
    manager->spare_heap_start = manager->spare_heap_next = heap2;
    manager->cur_heap_end     = heap1 + heap_size;
    manager->spare_heap_end   = heap2 + heap_size;

    void **arg_stack = calloc(arg_stack_size, sizeof(void*));
    manager->arg_stack_start = arg_stack;
    manager->arg_stack_end   = arg_stack + arg_stack_size;

    manager->indirection = indirection;
    manager->iproc = iproc;

    parse_stackmap(manager, stackmap);
}

