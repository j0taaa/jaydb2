#include "constructor_bridge.h"
#include <stddef.h>

#if !defined(__linux__) || !defined(__x86_64__)
#error Constructor bridge requires Linux x86_64
#endif
#ifndef JAYDB_CONSTRUCTOR_STACK_BYTES
#error Builder must supply the audited explicit stack extent
#endif
_Static_assert(sizeof(struct jayacct_snapshot)==120,"accounting ABI");

static __attribute__((always_inline)) inline long raw4(long nr,long a,long b,long c,long d) {
  register long r10 __asm__("r10")=d;
  long result;
  __asm__ volatile("syscall":"=a"(result):"a"(nr),"D"(a),"S"(b),"d"(c),"r"(r10)
                   :"rcx","r11","memory","cc");
  return result;
}
static __attribute__((always_inline)) inline void clear(void *p,size_t n) {
  volatile unsigned char *b=p;
  for(size_t i=0;i<n;++i)b[i]=0;
}
static __attribute__((always_inline)) inline __uint128_t nat(struct jayacct_u128 n) {
  return ((__uint128_t)n.hi<<64)|n.lo;
}
#ifdef JAYDB_CONSTRUCTOR_TEST
/* Test-only observations are synthetic and never a real measurement. */
extern int jaydb_constructor_test_marker(void *,uint64_t);
extern long jaydb_constructor_test_clock(long *);
#endif
static __attribute__((always_inline)) inline int marker(void *out,uint64_t op,
    struct jayacct_u128 deadline) {
#ifdef JAYDB_CONSTRUCTOR_TEST
  (void)deadline;
  return jaydb_constructor_test_marker(out,op);
#else
  return jayacct_raw_marker(out,op==JAYACCT_RELEASE_OPERATION?op:op|JAYACCT_UNTIL_FLAG,deadline);
#endif
}
static __attribute__((always_inline)) inline long clock_now(long *ts) {
#ifdef JAYDB_CONSTRUCTOR_TEST
  return jaydb_constructor_test_clock(ts);
#else
  return raw4(228,1,(long)ts,0,0);
#endif
}
struct context {
  const struct jaydb_constructor_span *spans;
  uint64_t count;
  struct jayacct_u128 ceiling,deadline;
  struct jaydb_constructor_result *result;
};
/* Production leaf: no coverage, callbacks, allocator, library calls, VLA or
 * nonlocal escape. Inputs, destinations and this stack are already active.
 * Loop bounds follow the actual prepared object, not an invented arity cap. */
static __attribute__((noinline)) void critical(void *arg) {
  struct context *c=arg;
  struct jaydb_constructor_result *r=c->result;
  struct jayacct_snapshot held;
  volatile long ts[2];
  uint64_t release_receipt=0;
  clear(&held,sizeof held);
  ts[0]=0;ts[1]=0;
  int error=marker(&held,1,c->deadline);
  if(error){r->instrument_error=(uint64_t)error;goto release;}
  error=marker(&r->memory,0,c->deadline);
  if(error){r->instrument_error=(uint64_t)error;goto release;}
  uint64_t flags=r->memory.flags;
  if(held.abi!=JAYACCT_ABI || r->memory.abi!=JAYACCT_ABI
      || nat(r->memory.sequence)<nat(held.sequence)) {
    r->instrument_error=EINVAL;goto release;
  }
  if((flags&(JAYACCT_FROZEN|JAYACCT_HELD))!=(JAYACCT_FROZEN|JAYACCT_HELD)
      || (flags&(JAYACCT_INCOMPLETE|JAYACCT_OWNER_DIED))) {
    r->status=JAYDB_CONSTRUCTOR_COVERAGE;goto release;
  }
  if(nat(r->memory.current)>nat(c->ceiling)) {
    r->status=JAYDB_CONSTRUCTOR_MEMORY;goto release;
  }
  long ce=clock_now((long *)ts);
  if(ce<0 || ts[0]<0 || ts[1]<0 || ts[1]>=1000000000L) {
    r->clock_error=(uint64_t)(ce<0?-ce:EINVAL);goto release;
  }
  __uint128_t now=(__uint128_t)(unsigned long)ts[0]*1000000000u+(unsigned long)ts[1];
  r->checked_ns=(struct jayacct_u128){(uint64_t)now,(uint64_t)(now>>64)};
  if(now>=nat(c->deadline)){r->status=JAYDB_CONSTRUCTOR_TIME;goto release;}
  /* Actual object construction, after the final complete global observation.
   * Byte stores cannot lower to an allocating/interposed memcpy. All values
   * were prepared before entry; no emitted constructor or lookup is called. */
  for(uint64_t i=0;i<c->count;++i) {
    volatile unsigned char *destination=c->spans[i].destination;
    const unsigned char *source=c->spans[i].source;
    for(uint64_t j=0;j<c->spans[i].bytes;++j)destination[j]=source[j];
  }
  /* Completion receipt, not a definition/filter of semantic Campo events.
   * Every partial destination store above already happened while held. */
  __atomic_store_n(&r->constructed,1,__ATOMIC_RELEASE);
  r->status=JAYDB_CONSTRUCTED;
release:
  if(r->status==JAYDB_CONSTRUCTOR_INSTRUMENT && r->instrument_error==ETIMEDOUT) {
    long ce=clock_now((long *)ts);
    if(!ce && ts[0]>=0 && ts[1]>=0 && ts[1]<1000000000L) {
      __uint128_t now=(__uint128_t)(unsigned long)ts[0]*1000000000u+(unsigned long)ts[1];
      r->checked_ns=(struct jayacct_u128){(uint64_t)now,(uint64_t)(now>>64)};
      if(now>=nat(c->deadline))r->status=JAYDB_CONSTRUCTOR_TIME;
    }
  }
  error=marker(&release_receipt,JAYACCT_RELEASE_OPERATION,c->deadline);
  if(error)r->release_error=(uint64_t)error;
}

extern void jaydb_constructor_on_stack(void (*)(void *),void *,void *);
uint64_t jaydb_constructor_stack_bytes(void){return JAYDB_CONSTRUCTOR_STACK_BYTES;}
uint64_t jaydb_constructor_transfer(uint64_t cid,uint64_t site,
    const struct jaydb_length_checked *length,const struct jaydb_constructor_span *spans,
    uint64_t count,struct jayacct_u128 ceiling,struct jayacct_u128 deadline,
    void *stack,uint64_t bytes,struct jaydb_constructor_result *r) {
  if(!r)return JAYDB_CONSTRUCTOR_ARGUMENT;
  clear(r,sizeof *r);r->status=JAYDB_CONSTRUCTOR_ARGUMENT;
  if(!length || length->abi!=JAYDB_CONSTRUCTOR_ABI || length->checked!=1
      || !spans || !count || count>SIZE_MAX/sizeof *spans
      || !stack || ((uintptr_t)stack&15) || bytes<JAYDB_CONSTRUCTOR_STACK_BYTES
      || bytes>UINTPTR_MAX-(uintptr_t)stack)return r->status;
  for(uint64_t i=0;i<count;++i) {
    if(!spans[i].destination || !spans[i].source || !spans[i].bytes
        || spans[i].bytes>UINTPTR_MAX-(uintptr_t)spans[i].destination
        || spans[i].bytes>UINTPTR_MAX-(uintptr_t)spans[i].source)return r->status;
  }
  r->constructor_id=cid;r->site_id=site;r->position=length->position;r->quantity=length->quantity;
  struct context c={spans,count,ceiling,deadline,r};
  uint64_t all=UINT64_MAX,previous=0;
  long error=raw4(14,0,(long)&all,(long)&previous,8);
  r->status=JAYDB_CONSTRUCTOR_INSTRUMENT;
  if(error<0){r->instrument_error=(uint64_t)-error;return r->status;}
  jaydb_constructor_on_stack(critical,&c,(char *)stack+bytes);
  error=raw4(14,2,(long)&previous,0,8);
  if(error<0)r->release_error=(uint64_t)-error;
  return r->status;
}
