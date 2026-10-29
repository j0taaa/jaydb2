#ifndef JAYDB_DECODER_MEMORY_H
#define JAYDB_DECODER_MEMORY_H
#include <stdint.h>
struct jaydb_decoder_memory { struct jaydb_decoder_memory *next; void *mapping; uint64_t bytes,reserved; };
/* Uncovered support: acquisition, owner metadata and linking finish before a
 * poll/nonlocal escape. No preventive budget check in accounted mode. */
uint32_t jaydb_decoder_acquire(struct jaydb_decoder_memory **,uint64_t,void **);
uint32_t jaydb_decoder_acquire_backing(struct jaydb_decoder_memory **,struct jaydb_decoder_memory *,uint64_t,void **);
void jaydb_decoder_release_one(struct jaydb_decoder_memory **);
#endif
