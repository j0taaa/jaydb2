/* Synthetic marker observations for unit tests; never a real memory measure. */
#include "../../native/constructor_bridge.h"
static uint64_t flags=9,sequence=10,current=100,now=100;
static uint64_t failure_op=UINT64_MAX,failure_error,releases;
static volatile unsigned char *watched;
static uint64_t watched_bytes,modified_before_final;
void jaydb_constructor_fixture(uint64_t f,uint64_t n,uint64_t t,uint64_t op,uint64_t error) {
  flags=f;current=n;now=t;failure_op=op;failure_error=error;
  sequence=10;releases=0;modified_before_final=0;
}
void jaydb_constructor_watch(void *p,uint64_t bytes){watched=p;watched_bytes=bytes;}
uint64_t jaydb_constructor_fixture_count(unsigned selector) {
  return selector?modified_before_final:releases;
}
int jaydb_constructor_test_marker(void *out,uint64_t op) {
  if(op==JAYACCT_RELEASE_OPERATION){++releases;return failure_op==op?(int)failure_error:0;}
  if(failure_op==op)return (int)failure_error;
  for(uint64_t i=0;i<watched_bytes;++i)if(watched[i]!=0xa5)++modified_before_final;
  struct jayacct_snapshot *s=out;
  *s=(struct jayacct_snapshot){.abi=JAYACCT_ABI,.sequence={++sequence,0},
    .current={current,0},.peak={current,0},.monotonic_ns={now,0},.flags=flags};
  return 0;
}
long jaydb_constructor_test_clock(long *ts){ts[0]=0;ts[1]=(long)now;return 0;}
