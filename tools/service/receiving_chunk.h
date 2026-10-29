#ifndef JAYDB_RECEIVING_CHUNK_H
#define JAYDB_RECEIVING_CHUNK_H
#include <stdint.h>
#include <stdatomic.h>
struct jaydb_receiving_chunk_u128_v1 {uint64_t lo,hi;};
struct jaydb_receiving_chunk_request_v1 {
  int32_t fd;uint32_t reserved;uintptr_t buffer;uint64_t quantity;
  struct jaydb_receiving_chunk_u128_v1 deadline;
};
struct jaydb_receiving_chunk_receipt_v1 {
  uint32_t abi;_Atomic uint32_t state;uint32_t status,system_error;
  uint64_t received;
  struct jaydb_receiving_chunk_u128_v1 started,returned;
};
enum {JAYDB_CHUNK_READY,JAYDB_CHUNK_CALLING,JAYDB_CHUNK_RETURNED};
enum {JAYDB_CHUNK_OK,JAYDB_CHUNK_EOF,JAYDB_CHUNK_INTERRUPTED,JAYDB_CHUNK_IO,JAYDB_CHUNK_TIME,JAYDB_CHUNK_ARGUMENT,JAYDB_CHUNK_BUSY};
uint32_t jaydb_receiving_chunk_read_v1(const struct jaydb_receiving_chunk_request_v1*,struct jaydb_receiving_chunk_receipt_v1*);
_Static_assert(sizeof(struct jaydb_receiving_chunk_request_v1)==40,"request");
_Static_assert(sizeof(struct jaydb_receiving_chunk_receipt_v1)==56,"receipt");
/* One request/receipt pair is used once. Storage and fd are owned by the
 * trusted caller for the entire call. A RETURNED receipt survives exceptions
 * at FFI return; CALLING is uncertain and never authorizes another read.
 * No allocation occurs here. Readiness, sole-reader ownership, backing and
 * whole-stage interruption remain obligations of the host. */
struct jaydb_receiving_chunk_descriptor_v1 {
  uint64_t abi,request_bytes,receipt_bytes,flags;
  const char *build_identity_sha256;
};
const struct jaydb_receiving_chunk_descriptor_v1 *jaydb_receiving_chunk_describe_v1(void);
#endif
