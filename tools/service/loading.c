#include "loading.h"
#include <dlfcn.h>
#include <stddef.h>

#ifndef JAYDB_LOADING_BUILD_ID
#error "Build through build_loading.py with an explicit source identity"
#endif

_Static_assert(sizeof(void *) == 8, "ABI 1 requires the Linux 64-bit host");
_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "Receipt state must be lock-free");
_Static_assert(ATOMIC_LLONG_LOCK_FREE == 2, "Receipt outcome must be lock-free");
_Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "ABI 1 is little-endian");
_Static_assert(sizeof(jaydb_loading_open_receipt_v1) == 24, "open receipt ABI");
_Static_assert(sizeof(jaydb_loading_close_receipt_v1) == 16, "close receipt ABI");
_Static_assert(sizeof(jaydb_loading_descriptor_v1) == 96, "descriptor ABI");
_Static_assert(offsetof(jaydb_loading_open_receipt_v1, handle) == 16, "handle ABI");

static const jaydb_loading_descriptor_v1 descriptor = {
    JAYDB_LOADING_ABI, sizeof(jaydb_loading_descriptor_v1),
    sizeof(jaydb_loading_open_receipt_v1), sizeof(jaydb_loading_close_receipt_v1),
    sizeof(void *), 0, JAYDB_LOADING_NODELETE, JAYDB_LOADING_BUILD_ID
};

const jaydb_loading_descriptor_v1 *jaydb_loading_describe_v1(void) {
    return &descriptor;
}

static uint64_t outcome(int32_t status) {
    return ((uint64_t)(uint32_t)status << 32) | 1;
}

static int completed_result(uint64_t result) {
    if (!(uint32_t)result)
        return JAYDB_LOADING_UNCERTAIN;
    return (int32_t)(result >> 32) == 0 ? JAYDB_LOADING_OK : JAYDB_LOADING_DL_ERROR;
}

int jaydb_loading_open_v1(const char *path, int mode,
                          jaydb_loading_open_receipt_v1 *receipt) {
    if (!receipt || receipt->abi != JAYDB_LOADING_ABI)
        return JAYDB_LOADING_BAD_ABI;
    uint32_t expected = 0;
    if (!atomic_compare_exchange_strong(&receipt->entered, &expected, 1)) {
        return completed_result(atomic_load_explicit(&receipt->outcome, memory_order_acquire));
    }
    void *handle = dlopen(path, mode);
    receipt->handle = (uintptr_t)handle;
    /* This is the durable result, before ctypes/Python can dispatch a signal. */
    atomic_store_explicit(&receipt->outcome, outcome(handle ? 0 : -1), memory_order_release);
    return handle ? JAYDB_LOADING_OK : JAYDB_LOADING_DL_ERROR;
}

int jaydb_loading_close_v1(const jaydb_loading_open_receipt_v1 *opened,
                           jaydb_loading_close_receipt_v1 *closed) {
    if (!opened || !closed || opened->abi != JAYDB_LOADING_ABI ||
        closed->abi != JAYDB_LOADING_ABI)
        return JAYDB_LOADING_BAD_ABI;
    uint64_t open_result = atomic_load_explicit(&opened->outcome, memory_order_acquire);
    if (!(uint32_t)open_result)
        return atomic_load(&opened->entered) ? JAYDB_LOADING_UNCERTAIN : JAYDB_LOADING_NOT_OPEN;
    if ((int32_t)(open_result >> 32) || !opened->handle)
        return JAYDB_LOADING_NOT_OPEN;

    uint32_t expected = 0;
    if (!atomic_compare_exchange_strong(&closed->entered, &expected, 1)) {
        uint64_t prior = atomic_load_explicit(&closed->outcome, memory_order_acquire);
        int result = completed_result(prior);
        if (result == JAYDB_LOADING_UNCERTAIN)
            return result;
        if (result == JAYDB_LOADING_OK)
            return JAYDB_LOADING_OK; /* the reference has already been consumed */
        /* A dlclose error returned without consuming the reference. Only one
         * caller may retry it. Others see an uncertain/in-progress receipt.
         */
        /* Compare the WHOLE outcome. A concurrent successful retry must never
         * be mistaken for the previous failure (and followed by another close).
         */
        if (!atomic_compare_exchange_strong(&closed->outcome, &prior, 0))
            return JAYDB_LOADING_UNCERTAIN;
    }
    int status = dlclose((void *)opened->handle);
    atomic_store_explicit(&closed->outcome, outcome(status), memory_order_release);
    return status == 0 ? JAYDB_LOADING_OK : JAYDB_LOADING_DL_ERROR;
}
