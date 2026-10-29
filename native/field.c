#include "field.h"
#include <stddef.h>
#if !defined(__linux__) || !defined(__x86_64__)
#error Field boundary requires Linux x86_64
#endif
#ifndef JAYDB_FIELD_STACK_BYTES
#error Builder must supply the audited stack extent
#endif
_Static_assert(sizeof(struct jayacct_snapshot)==120,"legacy snapshot ABI");
_Static_assert(sizeof(struct jayacct_window_snapshot)==280,"window ABI");
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
#ifdef JAYDB_FIELD_TEST
/* Separate fixture artifacts only. These symbols never enter production. */
extern int jaydb_field_test_marker(void *,uint64_t,struct jayacct_u128);
extern long jaydb_field_test_clock(long *);
extern long jaydb_field_test_map(uint64_t);
#endif
INLINE int marker(void *out,uint64_t op,struct jayacct_u128 deadline) {
#ifdef JAYDB_FIELD_TEST
  return jaydb_field_test_marker(out,op,deadline);
#else
  return jayacct_raw_marker(out,op==6?op:op|JAYACCT_UNTIL_FLAG,deadline);
#endif
}
INLINE long clock_now(long *ts) {
#ifdef JAYDB_FIELD_TEST
  return jaydb_field_test_clock(ts);
#else
  return raw6(228,1,(long)ts,0,0,0,0);
#endif
}
/* Raw clocks poll acquisitions and store prefixes with the same epoch.
 * The cadence limits syscall cost; no count/arity value itself refuses. */
INLINE int expired(struct jaydb_field_result *r,struct jayacct_u128 deadline) {
  volatile long ts[2];ts[0]=0;ts[1]=0;long e=clock_now((long *)ts);
  if(e<0 || ts[0]<0 || ts[1]<0 || ts[1]>=1000000000L) {
    r->clock_error=(uint64_t)(e<0?-e:EINVAL);r->status=JAYDB_FIELD_INSTRUMENT;return 1;
  }
  __uint128_t now=(__uint128_t)(unsigned long)ts[0]*1000000000u+(unsigned long)ts[1];
  if(now<nat(deadline))return 0;
  r->checked_ns=words(now);r->status=JAYDB_FIELD_TIME;return 1;
}
INLINE long map_backing(uint64_t n) {
#ifdef JAYDB_FIELD_TEST
  return jaydb_field_test_map(n);
#else
  /* This acquisition is exactly the missing destination extent. No quota,
   * calloc, lazy PROT_NONE reservation, or ceiling-dependent padding. */
  return raw6(9,0,(long)n,3,0x22,-1,0);
#endif
}
struct context {
  const struct jaydb_field_request *q;
  struct jaydb_field_result *r;
};
/* Audited in LLVM and the final object. No calls, VLA or automatic grow-down
 * stack accesses; acquisition is before the FINAL barrier. */
static __attribute__((noinline)) void field_critical(void *argument) {
  struct context *c=argument;
  const struct jaydb_field_request *q=c->q;
  struct jaydb_field_result *r=c->r;
  const struct jaydb_field_wire *w=&q->wire;
  struct jayacct_snapshot held;
  volatile long ts[2];
  uint64_t receipt=0;
  clear(&held,sizeof held);ts[0]=0;ts[1]=0;
  /* Effective wire check, not acceptance of a caller's checked boolean. */
  uint64_t pos=w->position,tag=w->bytes[pos],n=0,header=1;
  r->position=pos;r->tag=tag;
  if(tag>6 || (w->name && tag!=4)){r->status=JAYDB_FIELD_INPUT;return;}
  if(tag>=4) {
    if(w->size-pos<9){r->status=JAYDB_FIELD_INPUT;return;}
    header=9;
    for(uint64_t i=1;i<9;++i)n=(n<<8)|w->bytes[pos+i];
  } else if(tag==3)n=8;
  r->quantity=n;
  __uint128_t own=(__uint128_t)n*(tag==6?11u:1u);
  /* Only variable headers confer the pending minimum in Codec. Primitive
   * tags, including the fixed eight-byte integer, check their own extent. */
  __uint128_t pending=tag>=4?nat(w->pending_minimum):0;
  if(w->size>w->limit || pending>~(__uint128_t)0-own
      || own+pending>(__uint128_t)(w->limit-pos-header)) {
    r->status=JAYDB_FIELD_LENGTH;return;
  }
  if(own+pending>(__uint128_t)(w->size-pos-header)) {
    r->status=JAYDB_FIELD_INPUT;return;
  }
  if(w->name && (!n || n>64)){r->status=JAYDB_FIELD_INPUT;return;}
  r->length_checked=1;
  int error=marker(&held,1,q->deadline);
  if(error){r->instrument_error=(uint64_t)error;goto release;}
  if(held.abi!=JAYACCT_ABI || !nat(held.sequence)) {
    r->instrument_error=EINVAL;goto release;
  }
  /* Resolve/acquire raw storage BEFORE any logical claim or object store.
   * Multiple spans of one arena owner acquire backing once. */
  for(uint64_t i=0;i<q->owner_count;++i) {
    if(expired(r,q->deadline))goto release;
    struct jaydb_field_owner *owner=&q->owners[i];
    uint64_t need=0;
    for(uint64_t j=0;j<q->span_count;++j) {
      if(j && !(j%1024) && expired(r,q->deadline))goto release;
      if(q->spans[j].owner==i) {
        uint64_t end=q->spans[j].offset+q->spans[j].bytes;
        if(end>need)need=end;
      }
    }
    if(!owner->address && need) {
      uint64_t bytes=(need+4095u)&~UINT64_C(4095);
      long address=map_backing(bytes);
      if(address<0 && address>=-4095) {
        r->backing_error=(uint64_t)-address;r->status=JAYDB_FIELD_BACKING;goto release;
      }
      owner->address=(void *)address;owner->capacity=bytes;
      r->acquired_bytes+=bytes;
    }
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
  /* No allocator, lookup, library or callback from here through completion.
   * A first store is an actual construction even if transfer never completes. */
  __atomic_store_n(&r->construction_started,1,__ATOMIC_RELEASE);
  for(uint64_t i=0;i<q->span_count;++i) {
    const struct jaydb_field_span *s=&q->spans[i];
    volatile unsigned char *to=(unsigned char *)q->owners[s->owner].address+s->offset;
    const unsigned char *from=s->source;
    for(uint64_t j=0;j<s->bytes;++j) {
      if(!(j%4096) && expired(r,q->deadline))goto release;
      to[j]=from[j];++r->stores_completed;
    }
  }
  __atomic_store_n(&r->constructed,1,__ATOMIC_RELEASE);
  r->status=JAYDB_FIELD_CONSTRUCTED;
  (void)expired(r,q->deadline); /* a complete transfer is never erased */
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

/* Pointer-range checks are before hold; they do not assert page activation or
 * authenticate trusted host records. Those remain host/environment duties. */
static int range(const void *p,uint64_t n){return p && n && n<=UINTPTR_MAX-(uintptr_t)p;}
static int overlaps(const void *a,uint64_t an,const void *b,uint64_t bn) {
  return (uintptr_t)a<(uintptr_t)b+bn && (uintptr_t)b<(uintptr_t)a+an;
}
extern void jaydb_field_on_stack(void (*)(void *),void *,void *);
uint64_t jaydb_field_stack_bytes_v2(void){return JAYDB_FIELD_STACK_BYTES;}
uint64_t jaydb_field_construct_v2(const struct jaydb_field_request *q,
    void *stack,uint64_t bytes,struct jaydb_field_result *r) {
  if(!r)return JAYDB_FIELD_ARGUMENT;
  clear(r,sizeof *r);r->status=JAYDB_FIELD_ARGUMENT;
  if(!q || q->abi!=JAYDB_FIELD_ABI || !nat(q->scope) || q->wire.name>1
      || !range(q->wire.bytes,q->wire.size) || q->wire.position>=q->wire.size
      || !q->owners || !q->owner_count || q->owner_count>SIZE_MAX/sizeof *q->owners
      || !q->spans || !q->span_count || q->span_count>SIZE_MAX/sizeof *q->spans
      || !range(stack,bytes) || ((uintptr_t)stack&15) || bytes<JAYDB_FIELD_STACK_BYTES)
    return r->status;
  uint64_t owner_bytes=q->owner_count*sizeof *q->owners,span_bytes=q->span_count*sizeof *q->spans;
  if(!range(q->owners,owner_bytes) || !range(q->spans,span_bytes))return r->status;
  const void *records[]={q,r,q->owners,q->spans,q->wire.bytes,stack};
  uint64_t sizes[]={sizeof *q,sizeof *r,owner_bytes,span_bytes,q->wire.size,bytes};
  for(unsigned i=0;i<6;++i)for(unsigned j=0;j<i;++j)
    if(overlaps(records[i],sizes[i],records[j],sizes[j]))return r->status;
  for(uint64_t i=0;i<q->owner_count;++i) {
    if(i && !(i%1024) && expired(r,q->deadline))return r->status;
    const struct jaydb_field_owner *o=&q->owners[i];
    if((!o->address && o->capacity) || (o->address && !range(o->address,o->capacity)))return r->status;
    if(o->address) {
      for(unsigned j=0;j<6;++j)if(overlaps(o->address,o->capacity,records[j],sizes[j]))return r->status;
      for(uint64_t j=0;j<i;++j) {
        if(j && !(j%1024) && expired(r,q->deadline))return r->status;
        if(q->owners[j].address
            && overlaps(o->address,o->capacity,q->owners[j].address,q->owners[j].capacity))return r->status;
      }
    }
  }
  for(uint64_t i=0;i<q->span_count;++i) {
    if(i && !(i%1024) && expired(r,q->deadline))return r->status;
    const struct jaydb_field_span *s=&q->spans[i];
    if(s->owner>=q->owner_count || !range(s->source,s->bytes)
        || s->offset>UINT64_MAX-s->bytes || s->offset+s->bytes>UINT64_MAX-4095)return r->status;
    const struct jaydb_field_owner *o=&q->owners[s->owner];
    if(o->address && s->offset+s->bytes>o->capacity)return r->status;
    for(unsigned j=0;j<6;++j)if((j==1 || j==2 || j==5)
        && overlaps(s->source,s->bytes,records[j],sizes[j]))return r->status;
    for(uint64_t j=0;j<q->owner_count;++j) {
      if(j && !(j%1024) && expired(r,q->deadline))return r->status;
      if(q->owners[j].address
          && overlaps(s->source,s->bytes,q->owners[j].address,q->owners[j].capacity))return r->status;
    }
    for(uint64_t j=0;j<i;++j) {
      if(j && !(j%1024) && expired(r,q->deadline))return r->status;
      if(s->owner==q->spans[j].owner
          && s->offset<q->spans[j].offset+q->spans[j].bytes
          && q->spans[j].offset<s->offset+s->bytes)return r->status;
    }
  }
  struct context c={q,r};
  uint64_t all=UINT64_MAX,previous=0;
  long error=raw6(14,0,(long)&all,(long)&previous,8,0,0);
  r->status=JAYDB_FIELD_INSTRUMENT;
  if(error<0){r->instrument_error=(uint64_t)-error;return r->status;}
  jaydb_field_on_stack(field_critical,&c,(char *)stack+bytes);
  error=raw6(14,2,(long)&previous,0,8,0,0);
  if(error<0)r->release_error=(uint64_t)-error;
  return r->status;
}
