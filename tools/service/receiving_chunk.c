#include "receiving_chunk.h"
#if !defined(__linux__) || !defined(__x86_64__)
#error selected Linux x86_64 runtime only
#endif
static inline __attribute__((always_inline)) long raw3(long nr,long a,long b,long c) {
  long out;
  __asm__ volatile("syscall":"=a"(out):"a"(nr),"D"(a),"S"(b),"d"(c):"rcx","r11","cc","memory");
  return out;
}
static inline __attribute__((always_inline)) __uint128_t nat(struct jaydb_receiving_chunk_u128_v1 x){return ((__uint128_t)x.hi<<64)|x.lo;}
static inline __attribute__((always_inline)) struct jaydb_receiving_chunk_u128_v1 words(__uint128_t x){return (struct jaydb_receiving_chunk_u128_v1){x,x>>64};}
static inline __attribute__((always_inline)) long sample(struct jaydb_receiving_chunk_u128_v1 *out){
  long ts[2]={0,0};long e=raw3(228,1,(long)ts,0);
  if(e<0)return -e;
  if(ts[0]<0||ts[1]<0||ts[1]>=1000000000)return 22;
  *out=words((__uint128_t)(unsigned long)ts[0]*1000000000+(unsigned long)ts[1]);
  return 0;
}
#ifdef JAYDB_RECEIVING_TEST
extern void jaydb_receiving_test_chunk_completed(void);
#endif
uint32_t jaydb_receiving_chunk_read_v1(const struct jaydb_receiving_chunk_request_v1 *q,struct jaydb_receiving_chunk_receipt_v1 *r){
  if(!r||r->abi!=1)return JAYDB_CHUNK_ARGUMENT;
  uint32_t expected=JAYDB_CHUNK_READY;
  if(!atomic_compare_exchange_strong_explicit(&r->state,&expected,JAYDB_CHUNK_CALLING,memory_order_acq_rel,memory_order_acquire))return JAYDB_CHUNK_BUSY;
  r->status=JAYDB_CHUNK_ARGUMENT;r->system_error=0;r->received=0;
  r->started=(struct jaydb_receiving_chunk_u128_v1){0,0};r->returned=(struct jaydb_receiving_chunk_u128_v1){0,0};
  if(!q||q->fd<0||q->reserved||!q->buffer||!q->quantity||q->quantity>INT64_MAX
      ||q->buffer>UINTPTR_MAX-q->quantity||!nat(q->deadline))goto done;
  long e=sample(&r->started);
  if(e){r->status=JAYDB_CHUNK_IO;r->system_error=(uint32_t)e;goto done;}
  if(nat(r->started)>=nat(q->deadline)){r->status=JAYDB_CHUNK_TIME;r->returned=r->started;goto done;}
  long n=raw3(0,q->fd,(long)q->buffer,(long)q->quantity);
  if(n<0){r->status=n==-4?JAYDB_CHUNK_INTERRUPTED:JAYDB_CHUNK_IO;r->system_error=(uint32_t)-n;}
  else {r->received=(uint64_t)n;r->status=n?JAYDB_CHUNK_OK:JAYDB_CHUNK_EOF;}
  e=sample(&r->returned);
  if(e){r->status=JAYDB_CHUNK_IO;r->system_error=(uint32_t)e;goto done;}
  if(n>0&&nat(r->returned)>=nat(q->deadline))r->status=JAYDB_CHUNK_TIME;
done:
  atomic_store_explicit(&r->state,JAYDB_CHUNK_RETURNED,memory_order_release);
#ifdef JAYDB_RECEIVING_TEST
  jaydb_receiving_test_chunk_completed();
#endif
  return r->status;
}

#ifndef JAYDB_RECEIVING_BUILD_ID
#error "The builder must identify the loaded receiving artifact"
#endif
const struct jaydb_receiving_chunk_descriptor_v1 *jaydb_receiving_chunk_describe_v1(void){
  static const struct jaydb_receiving_chunk_descriptor_v1 d={1,40,56,
#ifdef JAYDB_RECEIVING_TEST
    1,
#else
    0,
#endif
    JAYDB_RECEIVING_BUILD_ID};
  return &d;
}
