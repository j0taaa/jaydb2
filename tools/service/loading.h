#ifndef JAYDB_SERVICE_LOADING_H
#define JAYDB_SERVICE_LOADING_H

/* Private Linux loader ABI 1. These receipts own ONE dlopen reference, even
 * when the FFI caller is interrupted. They must outlive the complete C call.
 * A caller must never reset a receipt or close its handle through another API.
 * entered && !returned is an uncertain operation, not permission to retry.
 * The host serializes use of a target library against destruction of its owner.
 * Destructors which do not return (longjmp, cancellation, process death) leave
 * an uncertain receipt. This ABI does not claim recovery from those effects.
 */
#include <stdint.h>
#include <stdatomic.h>

#define JAYDB_LOADING_ABI 1u
#define JAYDB_LOADING_NODELETE 1ull

typedef struct {
    uint32_t abi;
    _Atomic uint32_t entered;
    union {
        _Atomic uint64_t outcome; /* atomic pair: returned, status */
        struct { uint32_t returned; int32_t status; };
    };
    uintptr_t handle;
} jaydb_loading_open_receipt_v1;

typedef struct {
    uint32_t abi;
    _Atomic uint32_t entered;
    union {
        _Atomic uint64_t outcome;
        struct { uint32_t returned; int32_t status; };
    };
} jaydb_loading_close_receipt_v1;

typedef struct {
    uint32_t abi;
    uint32_t size;
    uint32_t open_receipt_bytes;
    uint32_t close_receipt_bytes;
    uint32_t pointer_bytes;
    uint32_t reserved;
    uint64_t flags;
    char build_identity[64];    /* hexadecimal SHA256, without a terminator */
} jaydb_loading_descriptor_v1;

enum jaydb_loading_result {
    JAYDB_LOADING_OK = 0,
    JAYDB_LOADING_DL_ERROR = 1,
    JAYDB_LOADING_BAD_ABI = 2,
    JAYDB_LOADING_UNCERTAIN = 3,
    JAYDB_LOADING_NOT_OPEN = 4
};

#define JAYDB_LOADING_EXPORT __attribute__((visibility("default")))
JAYDB_LOADING_EXPORT const jaydb_loading_descriptor_v1 *jaydb_loading_describe_v1(void);
JAYDB_LOADING_EXPORT int jaydb_loading_open_v1(const char *path, int mode,
                                             jaydb_loading_open_receipt_v1 *receipt);
JAYDB_LOADING_EXPORT int jaydb_loading_close_v1(const jaydb_loading_open_receipt_v1 *opened,
                                              jaydb_loading_close_receipt_v1 *closed);

#endif
