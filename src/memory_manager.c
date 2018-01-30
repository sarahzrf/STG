#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "memory_manager.h"

/* TODO figure out aliasing issues */

static int compare_statepoints(const void *v1, const void *v2) {
    const Statepoint *s1 = v1, *s2 = v2;
    if (s1->instruction < s2->instruction) return -1;
    else if (s1->instruction == s2->instruction) return 0;
    else return 1;
}

#define EAT_START(src) u8 *EAT_src = src
#define EAT_FROM(offset) size_t *EAT_offset = &offset
#define EAT(t, name) \
    t name; \
    memcpy(&name, EAT_src + *EAT_offset, sizeof(t)); \
    *EAT_offset += sizeof(t)
#define SKIP(t) *EAT_offset += sizeof(t)
#define ALIGN(t) \
    if (*EAT_offset % sizeof(t) != 0) \
    *EAT_offset += sizeof(t) - *EAT_offset % sizeof(t)
/* https://llvm.org/docs/StackMaps.html#stackmap-format */
static void parse_stackmap(Manager *manager, u8 *stackmap) {
    EAT_START(stackmap);
    size_t func_offset = 0;
    EAT_FROM(func_offset);

    /* header */
    EAT(u8, ver);
    SKIP(u8);
    SKIP(u16);
    assert(ver == 3);

    /* counts */
    EAT(u32, num_functions);
    EAT(u32, num_constants);
    EAT(u32, num_records);
    manager->statepoint_count = 0;
    /* this might be more than we need, I guess */
    manager->statepoints = calloc(num_records, sizeof(Statepoint));

    size_t record_offset = func_offset +
        S64 * 3 * num_functions + S64 * num_constants;

    for (; num_functions > 0; num_functions--) {
        EAT(u64, addr);
        EAT(u64, stack_size);
        EAT(u64, func_record_count);

        for (; func_record_count > 0; func_record_count--) {
            assert(num_records > 0);
            num_records--;

            EAT_FROM(record_offset);

            EAT(u64, patchpoint_id);
            EAT(u32, offset);
            SKIP(u16);
            EAT(u16, num_locations);
            assert(patchpoint_id == 2882400000);
            assert(num_locations >= 3 && num_locations % 2 == 1);

            u16 num_location_offsets = (num_locations - 3) / 2;
            i32 *location_offsets = calloc(num_location_offsets, sizeof(i32));

#define TYPE_SMALL_CONST 0x4
#define TYPE_INDIRECT    0x3
#define RSP_REGNUM       0x7
            for (int consts = 0; consts < 3; consts++) {
                EAT(u8, type);
                SKIP(u8);
                EAT(u16, size);
                SKIP(u16);
                SKIP(u16);
                EAT(i32, const_val);
                assert(type == TYPE_SMALL_CONST &&
                        size == S64 && const_val == 0);
            }

            for (u16 lo_ix = 0; lo_ix < num_location_offsets; lo_ix++) {
                EAT(u8, type);
                SKIP(u8);
                EAT(u16, size);
                EAT(u16, regnum);
                SKIP(u16);
                EAT(i32, offset);
                assert(type == TYPE_INDIRECT &&
                        size == S64 && regnum == RSP_REGNUM);

                EAT(u8, type2);
                SKIP(u8);
                EAT(u16, size2);
                EAT(u16, regnum2);
                SKIP(u16);
                EAT(i32, offset2);
                /* not sure I can actually rely on this in practice? */
                assert(type2 == type && size2 == size &&
                        regnum2 == regnum && offset2 == offset);

                location_offsets[lo_ix] = offset;
            }

            Statepoint s = {addr + offset, stack_size,
                num_location_offsets, location_offsets};
            manager->statepoints[manager->statepoint_count] = s;
            manager->statepoint_count++;

            ALIGN(u64);
            SKIP(u16);
            EAT(u16, num_live_outs);
            assert(num_live_outs == 0);
            ALIGN(u64);
        }
    }
    assert(num_records == 0);

    qsort(manager->statepoints,
            manager->statepoint_count, sizeof(Statepoint),
            compare_statepoints);
}

static Statepoint *find_statepoint(Manager *manager, u64 instr) {
    Statepoint s;
    s.instruction = instr;
    return bsearch(&s, manager->statepoints, manager->statepoint_count,
            sizeof(Statepoint), compare_statepoints);
}

u64 *setup_manager(Manager *manager,
        /* heap_size in u64s, arg_stack_size in entries */
        size_t heap_size, size_t arg_stack_size,
        u64 indirection, u64 iproc,
        u8 *stackmap) {
    manager->gc.in_progress = 0;

    u64 *space = calloc((heap_size * 2 + arg_stack_size) * S64, 1),
        *heap1 = space,
        *heap2 = heap1 + heap_size,
        *arg_stack = heap2 + heap_size;

    manager->cur_heap = (Heap){heap1, heap1, heap2};
    manager->spare_heap = (Heap){heap2, heap2, arg_stack};

    manager->arg_stack_start = arg_stack;

    manager->indirection = indirection;
    manager->iproc = iproc;

    parse_stackmap(manager, stackmap);

    return manager->arg_stack_start - 1;
}

static u64 *alloc(Manager *manager, size_t count);

/* The second arg is actually a double pointer, but since the pointed-to
 * pointer is stored in our giant array of u64s, we need to deref before
 * casting to respect aliasing rules. */
static void update(Manager *manager, u64 *ptr) {
    u64 *target = (u64*)*ptr;
    if ((u64)target == 0) return;
    while (target[0] == manager->indirection) {
        target = (u64*)target[1];
    }
    u64 *new_loc = target;
    if (!(manager->cur_heap.start <= target &&
                target < manager->cur_heap.end)) {
        size_t count = 2;
        if (target[0] != manager->iproc) count += target[1];
        new_loc = alloc(manager, count);
        memcpy(new_loc, target, count * S64);

        target[0] = manager->indirection;
        target[1] = (u64)new_loc;
    }
    *ptr = (u64)new_loc;
}

/* In this case, the double pointer is so that we can advance the caller's
 * pointer through the heap. */
static void update_fields(Manager *manager, u64 **ptr) {
    u64 *target = *ptr;
    assert(target[0] != manager->indirection);
    *ptr += 2;
    if (target[0] == manager->iproc) return;
    *ptr += target[1];
    for (size_t i = 0; i < target[1]; i++) {
        update(manager, &target[i + 2]);
    }
}

static void collect(Manager *manager) {
    /* fprintf(stderr, "collecting...\n"); */
    assert(!manager->gc.in_progress);
    manager->gc.in_progress = 1;

    Heap tmp = manager->spare_heap;
    tmp.next = tmp.start;
    manager->spare_heap = manager->cur_heap;
    manager->cur_heap = tmp;

    u8 *return_slot = manager->gc.caller_entry;
    for (;;) {
        u64 return_addr;
        memcpy(&return_addr, return_slot, S64);
        Statepoint *prev = find_statepoint(manager, return_addr);
        if (prev == NULL) break;
        u8 *rsp = return_slot + 8;
        for (u16 lo_ix = 0; lo_ix < prev->num_location_offsets; lo_ix++) {
            /* TODO this is probably UB??? */
            u64 *slot = (u64*)(rsp + prev->location_offsets[lo_ix]);
            update(manager, slot);
        }
        return_slot = rsp + prev->stack_size;
    }

    for (u64 *arg = manager->gc.arg_stack;
            arg >= manager->arg_stack_start; arg--) {
        update(manager, arg);
    }

    /* now iteratively copy over all transitively referenced objects */
    u64 *cur_obj = manager->cur_heap.start;
    while (cur_obj < manager->cur_heap.next) {
        update_fields(manager, &cur_obj);
    }

    size_t heap_size =
        (manager->spare_heap.end - manager->spare_heap.start) * S64;
    /* This is actually necessary for correctness. A closure is
     * allocated before its children, so if allocating one of its
     * children triggers a collection, it will have uninitialized
     * fields. In order to be able to handle that correctly, we need to
     * be able to assume that uninitialized fields will be 0, so we
     * need to wipe the old heap before it'll be suitable for future
     * reuse. */
    memset(manager->spare_heap.start, 0, heap_size);

    manager->gc.in_progress = 0;
}

/* count in u64s */
static u64 *alloc(Manager *manager, size_t count) {
    u64 *new_next = manager->cur_heap.next + count;
    if (new_next > manager->cur_heap.end) {
        collect(manager);
        new_next = manager->cur_heap.next + count;
        if (new_next > manager->cur_heap.end) {
            fprintf(stderr, "OOM!\n");
            return NULL;
        }
    }
    u64 *mem = manager->cur_heap.next;
    manager->cur_heap.next = new_next;
    return mem;
}

u64 *alloc_from(
        Manager *manager,
        u8 *caller_entry, u64 *arg_stack,
        size_t count) {
    manager->gc.caller_entry = caller_entry;
    manager->gc.arg_stack = arg_stack;
    return alloc(manager, count);
}

