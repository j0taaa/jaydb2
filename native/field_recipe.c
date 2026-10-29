#include "field_recipe.h"
#include <stddef.h>
#ifndef JAYDB_RECIPE_STACK_BYTES
#error The recipe builder must derive its explicit stack extent
#endif
_Static_assert(sizeof(struct jaydb_word192)==24,"Term carrier");
#define INLINE static __attribute__((always_inline)) inline
INLINE long raw6(long nr,long a,long b,long c,long d,long e,long f) {
  register long r10 __asm__("r10")=d;
  register long r8 __asm__("r8")=e;
  register long r9 __asm__("r9")=f;
  long result;
  __asm__ volatile("syscall":"=a"(result):"a"(nr),"D"(a),"S"(b),"d"(c),
    "r"(r10),"r"(r8),"r"(r9):"rcx","r11","memory","cc");
  return result;
}
INLINE void clear(void *p,size_t n) {
  volatile unsigned char *b=p;
  for(size_t i=0;i<n;++i)b[i]=0;
}
INLINE __uint128_t nat(struct jayacct_u128 n){return ((__uint128_t)n.hi<<64)|n.lo;}
INLINE struct jayacct_u128 words(__uint128_t n){return (struct jayacct_u128){n,n>>64};}
#ifdef JAYDB_RECIPE_TEST
/* Separate fixture artifacts only. These symbols never enter production. */
extern int jaydb_recipe_test_marker(void *,uint64_t,struct jayacct_u128);
extern long jaydb_recipe_test_clock(long *);
extern long jaydb_recipe_test_map(uint64_t);
#endif
INLINE int marker(void *out,uint64_t op,struct jayacct_u128 deadline) {
#ifdef JAYDB_RECIPE_TEST
  return jaydb_recipe_test_marker(out,op,deadline);
#else
  return jayacct_raw_marker(out,op==6?op:op|JAYACCT_UNTIL_FLAG,deadline);
#endif
}
INLINE long clock_now(long *ts) {
#ifdef JAYDB_RECIPE_TEST
  return jaydb_recipe_test_clock(ts);
#else
  return raw6(228,1,(long)ts,0,0,0,0);
#endif
}

/* Raw ordinary clocks also poll store prefixes while peers remain held.
 * No callback/library/allocation is introduced after FINAL. The cadence
 * limits syscall cost; no count/arity value itself refuses construction. */
INLINE int expired(struct jaydb_field_result *r,struct jayacct_u128 deadline) {
  volatile long ts[2];ts[0]=0;ts[1]=0;long e=clock_now((long *)ts);
  if(e<0 || ts[0]<0 || ts[1]<0 || ts[1]>=1000000000L) {
    r->clock_error=(uint64_t)(e<0?-e:EINVAL);r->status=JAYDB_FIELD_INSTRUMENT;return 1;
  }
  __uint128_t now=(__uint128_t)(unsigned long)ts[0]*1000000000u+(unsigned long)ts[1];
  if(now<nat(deadline))return 0;
  r->checked_ns=words(now);r->status=JAYDB_FIELD_TIME;return 1;
}

struct context { const struct jaydb_field_recipe *q; struct jaydb_field_result *r; };
static __attribute__((noinline)) void recipe_critical(void *argument) {
  struct context *c=argument;
  const struct jaydb_field_recipe *q=c->q;
  struct jaydb_field_result *r=c->r;
  const struct jaydb_field_wire *w=&q->wire;
  struct jayacct_snapshot held;
  volatile long ts[2];uint64_t receipt=0;
  clear(&held,sizeof held);ts[0]=0;ts[1]=0;
  uint64_t pos=w->position,tag=w->bytes[pos],n=0,header_bytes=1;
  r->position=pos;r->tag=tag;
  if(tag>6 || (w->name && tag!=4)){r->status=JAYDB_FIELD_INPUT;return;}
  if(tag>=4) {
    if(w->size-pos<9){r->status=JAYDB_FIELD_INPUT;return;}
    header_bytes=9;for(uint64_t i=1;i<9;++i)n=(n<<8)|w->bytes[pos+i];
  } else if(tag==3)n=8;
  r->quantity=n;
  /* Inteiro has a fixed eight-byte extent; primitive tags carry no declared
   * count. Their original Codec transitions do not consult pending siblings.
   * Recheck their own wire extent here, without adding a variable-header guard
   * that would alter the exact error/prefix. Variable tags retain the full
   * original pending-minimum test before every construction. */
  __uint128_t own=(__uint128_t)n*(tag==6?11u:1u);
  __uint128_t pending=tag>=4?nat(w->pending_minimum):0;
  if(n!=q->quantity || w->size>w->limit || pending>~(__uint128_t)0-own
      || own+pending>(__uint128_t)(w->limit-pos-header_bytes)) {
    r->status=JAYDB_FIELD_LENGTH;return;
  }
  if(own+pending>(__uint128_t)(w->size-pos-header_bytes) || (w->name && (!n || n>64))) {
    r->status=JAYDB_FIELD_INPUT;return;
  }
  r->length_checked=1;
  int error=marker(&held,1,q->deadline);
  if(error){r->instrument_error=(uint64_t)error;goto release;}
  if(held.abi!=JAYACCT_ABI || !nat(held.sequence)) {
    r->instrument_error=EINVAL;goto release;
  }
  error=marker(&r->window,5,q->deadline); /* FINAL, leave this scope ACTIVE */
  if(error){r->instrument_error=(uint64_t)error;goto release;}
  const struct jayacct_window_snapshot *v=&r->window;
  if(v->abi!=JAYACCT_WINDOW_ABI || v->snapshot.abi!=JAYACCT_ABI || v->state!=JAYACCT_WINDOW_ACTIVE
      || nat(v->scope_id)!=nat(q->scope) || !nat(v->begin_sequence)
      || nat(v->snapshot.sequence)<=nat(held.sequence)
      || nat(v->snapshot.monotonic_ns)<nat(held.monotonic_ns)
      || nat(v->begin_sequence)>nat(held.sequence)
      || nat(v->snapshot.sequence)<nat(v->begin_sequence)
      || nat(v->snapshot.monotonic_ns)<nat(v->begin_monotonic_ns)
      || nat(v->end_sequence) || nat(v->end_monotonic_ns)
      || nat(v->peak_sequence)<nat(v->begin_sequence)
      || nat(v->peak_sequence)>nat(v->snapshot.sequence)
      || nat(v->peak_monotonic_ns)<nat(v->begin_monotonic_ns)
      || nat(v->peak_monotonic_ns)>nat(v->snapshot.monotonic_ns)
      || nat(v->snapshot.current)>nat(v->peak)) {
    r->instrument_error=EINVAL;goto release;
  }
  uint64_t flags=v->snapshot.flags;
  if((flags&(JAYACCT_FROZEN|JAYACCT_HELD))!=(JAYACCT_FROZEN|JAYACCT_HELD)
      || !(v->peak_flags&JAYACCT_FROZEN)
      || ((flags|v->peak_flags)&(JAYACCT_INCOMPLETE|JAYACCT_OWNER_DIED))) {
    r->status=JAYDB_FIELD_COVERAGE;goto release;
  }
  if(nat(v->peak)>nat(q->ceiling)){r->status=JAYDB_FIELD_MEMORY;goto release;}
  long ce=clock_now((long *)ts);
  if(ce<0 || ts[0]<0 || ts[1]<0 || ts[1]>=1000000000L) {
    r->clock_error=(uint64_t)(ce<0?-ce:EINVAL);goto release;
  }
  __uint128_t now=(__uint128_t)(unsigned long)ts[0]*1000000000u+(unsigned long)ts[1];
  r->checked_ns=words(now);
  if(now<nat(v->snapshot.monotonic_ns)){r->clock_error=EINVAL;goto release;}
  if(now>=nat(q->deadline)){r->status=JAYDB_FIELD_TIME;goto release;}
  __atomic_store_n(&r->construction_started,1,__ATOMIC_RELEASE);
  if(q->claim) {
    *q->claim=q->claim_value;
    if(q->claim_count)++*q->claim_count;
  }
  if(q->operation==JAYDB_RECIPE_CTR)for(uint64_t i=0;i<q->count;++i) {
    if(!(i%128) && expired(r,q->deadline))goto release;
    volatile unsigned char *to=(void *)q->destinations[i];
    const unsigned char *from=(const void *)&q->components[i];
    for(uint64_t j=0;j<sizeof(struct jaydb_word192);++j)to[j]=from[j];
    r->stores_completed+=sizeof(struct jaydb_word192);
  }
  if(expired(r,q->deadline))goto release;
  volatile struct jaydb_word192 *header=q->header;
  header->payload=q->operation==JAYDB_RECIPE_CTR?q->location:
                    q->count?q->components[0].payload:0;
  header->auxiliary=q->operation==JAYDB_RECIPE_WORD?0:q->constructor_id;
  header->tag=q->operation;
  r->stores_completed+=sizeof *header;
  __atomic_store_n(&r->constructed,1,__ATOMIC_RELEASE);
  if(q->completed_count)++*q->completed_count;
  r->status=JAYDB_FIELD_CONSTRUCTED;
  (void)expired(r,q->deadline);
release:
  if(r->status==JAYDB_FIELD_INSTRUMENT && r->instrument_error==ETIMEDOUT) {
    long ce=clock_now((long *)ts);
    if(!ce && ts[0]>=0 && ts[1]>=0 && ts[1]<1000000000L) {
      __uint128_t now=(__uint128_t)(unsigned long)ts[0]*1000000000u+(unsigned long)ts[1];
      r->checked_ns=words(now);
      if(now>=nat(q->deadline))r->status=JAYDB_FIELD_TIME;
    } else r->clock_error=(uint64_t)(ce<0?-ce:EINVAL);
  }
  error=marker(&receipt,6,q->deadline);
  if(error)r->release_error=(uint64_t)error;
}


extern void jaydb_recipe_on_stack(void (*)(void *),void *,void *);
uint64_t jaydb_field_recipe_stack_v3(void){return JAYDB_RECIPE_STACK_BYTES;}
uint64_t jaydb_field_recipe_v3(const struct jaydb_field_recipe *q,void *stack,
    uint64_t bytes,struct jaydb_field_result *r) {
  if(!r)return JAYDB_FIELD_ARGUMENT;
  clear(r,sizeof *r);r->status=JAYDB_FIELD_ARGUMENT;
  if(!q || q->operation>2 || !nat(q->scope) || !q->header || !q->wire.bytes
      || q->wire.position>=q->wire.size || !stack || ((uintptr_t)stack&15)
      || bytes<JAYDB_RECIPE_STACK_BYTES || q->count>SIZE_MAX/sizeof *q->components
      || (q->count && !q->components)
      || (q->operation==2 && (!q->count || !q->destinations)))return r->status;
  /* Trusted adapter owns/disjoins all record ranges, and prepares only active
   * destinations. Public C is not accepted as an untrusted memory sandbox. */
  struct context c={q,r};uint64_t all=UINT64_MAX,previous=0;
  long error=raw6(14,0,(long)&all,(long)&previous,8,0,0);
  r->status=JAYDB_FIELD_INSTRUMENT;
  if(error<0){r->instrument_error=(uint64_t)-error;return r->status;}
  jaydb_recipe_on_stack(recipe_critical,&c,(char *)stack+bytes);
  error=raw6(14,2,(long)&previous,0,8,0,0);
  if(error<0)r->release_error=(uint64_t)-error;
  return r->status;
}
