#define _GNU_SOURCE
#include "decoder_memory.h"
#include "abi.h"
#include "leaves.h"
#include <sys/mman.h>
#include <stddef.h>
uint32_t jaydb_decoder_acquire(struct jaydb_decoder_memory **owners,uint64_t need,void **out) {
  if(need>SIZE_MAX-sizeof(struct jaydb_decoder_memory)-4095)return JAYDB_SYSTEM;
  uint64_t bytes=(need+sizeof(struct jaydb_decoder_memory)+4095)&~UINT64_C(4095);
  struct jaydb_decoder_memory *node=jaydb_os_mmap(0,bytes,3,0x22,-1,0);
  if(node==MAP_FAILED)return JAYDB_SYSTEM;
  node->next=*owners;node->mapping=node;node->bytes=bytes;*owners=node;*out=node+1;
  return JAYDB_OK;
}
void jaydb_decoder_release_one(struct jaydb_decoder_memory **owners) {
  struct jaydb_decoder_memory *node=*owners,*next=node->next;
  uint64_t bytes=node->bytes;
  void *mapping=node->mapping;
  jaydb_os_munmap(mapping,bytes);*owners=next;
}

uint32_t jaydb_decoder_acquire_backing(struct jaydb_decoder_memory **owners,
    struct jaydb_decoder_memory *record,uint64_t bytes,void **out) {
  void *mapping=jaydb_os_mmap(0,bytes,3,0x22,-1,0);
  if(mapping==MAP_FAILED)return JAYDB_SYSTEM;
  record->next=*owners;record->mapping=mapping;record->bytes=bytes;*owners=record;*out=mapping;
  return JAYDB_OK;
}
