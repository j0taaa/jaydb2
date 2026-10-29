#define _GNU_SOURCE
#include "../../native/field.h"
#include <unistd.h>
#include <sys/mman.h>
#include <signal.h>
/* SYNTHETIC observations; actual mmap is used only to test causal order.
 * This artifact is never linked or loaded as a production measurement. */
struct fixture {
  uint64_t flags,current,peak,global_peak,now,scope,peak_flags;
  uint64_t fail_op,error,map_error,release_error,clock_error,invalid,signal;
  uint64_t holds,finals,releases,maps,mapped_bytes,early_stores,closed;
  uint64_t deadlines[3];
  uint64_t maps_at_final,fail_map_index,clock_calls,advance_at,advance_ns;
};
static struct fixture f;
static const unsigned char *watched;
static uint64_t watched_bytes;
void *jaydb_field_fixture(void) {
  f=(struct fixture){.flags=9,.current=100,.peak=100,.global_peak=10000,
    .now=100,.scope=7,.peak_flags=1,.fail_op=UINT64_MAX};
  watched=0;watched_bytes=0;
  return &f;
}
void jaydb_field_watch(const void *p,uint64_t n){watched=p;watched_bytes=n;}
int jaydb_field_test_marker(void *out,uint64_t op,struct jayacct_u128 until) {
  if(op==6){++f.releases;return (int)f.release_error;}
  for(uint64_t i=0;i<watched_bytes;++i)if(watched[i]!=0xa5)++f.early_stores;
  if(op==1){++f.holds;f.deadlines[0]=until.lo;}
  if(op==5){++f.finals;f.deadlines[1]=until.lo;f.maps_at_final=f.maps;}
  if(op==4)++f.closed;
  *(uint64_t *)out=0;
  if(op==f.fail_op)return (int)f.error;
  struct jayacct_snapshot s={.abi=1,.sequence={op==1?11:12,0},
    .current={f.current,0},.peak={f.global_peak,0},.monotonic_ns={100,0},.flags=f.flags};
  if(op==1){*(struct jayacct_snapshot *)out=s;return 0;}
  if(op!=5)return EINVAL;
  struct jayacct_window_snapshot *v=out;
  *v=(struct jayacct_window_snapshot){.abi=1,.state=1,.snapshot=s,
    .scope_id={f.scope,0},.begin_sequence={10,0},.begin_monotonic_ns={50,0},
    .peak={f.peak,0},.peak_monotonic_ns={80,0},.peak_sequence={11,0},.peak_flags=f.peak_flags};
  if(f.invalid==1)v->state=2;
  if(f.invalid==2)v->begin_sequence.lo=13;
  if(f.invalid==3)v->peak_sequence.lo=9;
  if(f.invalid==4)v->peak_monotonic_ns.lo=101;
  if(f.invalid==5)v->end_sequence.lo=12;
  if(f.invalid==6)v->snapshot.abi=0;
  if(f.signal)kill(getpid(),(int)f.signal);
  return 0;
}
long jaydb_field_test_clock(long *ts) {
  if(f.clock_error)return -(long)f.clock_error;
  ++f.clock_calls;
  uint64_t now=f.now+(f.advance_at && f.clock_calls>=f.advance_at?f.advance_ns:0);
  ts[0]=(long)(now/1000000000u);ts[1]=(long)(now%1000000000u);return 0;
}
long jaydb_field_test_map(uint64_t n) {
  ++f.maps;f.mapped_bytes+=n;
  if(f.map_error && (!f.fail_map_index || f.maps==f.fail_map_index))return -(long)f.map_error;
  void *p=mmap(0,n,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  return p==MAP_FAILED?-ENOMEM:(long)p;
}
