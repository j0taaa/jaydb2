/* Numeric/temporal unit fixture only. Not a measurement adapter. */
#include "../../tools/service/commit.h"
#include <errno.h>
#include <stddef.h>
#include <signal.h>
static struct jayacct_window_snapshot sample;
static uint64_t tick, hold_error, close_error, release_error;
static uint64_t holds, closes, releases;
static int clock_signal;
void jaydb_commit_fixture_signal(int number) {clock_signal=number;}
void jaydb_commit_fixture(uint64_t flags,uint64_t scope,uint64_t current,uint64_t peak,
    uint64_t now,uint64_t begin_fail,uint64_t close_fail,uint64_t release_fail) {
  sample=(struct jayacct_window_snapshot){.abi=1,.state=JAYACCT_WINDOW_CLOSED,
    .snapshot={.abi=1,.sequence={30,0},.monotonic_ns={30,0},.current={current,0},.flags=flags},
    .scope_id={scope,0},.begin_sequence={10,0},.begin_monotonic_ns={10,0},
    .end_sequence={30,0},.end_monotonic_ns={30,0},
    .peak={peak,0},.peak_monotonic_ns={20,0},.peak_sequence={20,0},.peak_flags=flags};
  tick=now;hold_error=begin_fail;close_error=close_fail;release_error=release_fail;
  holds=closes=releases=0;clock_signal=0;
}
uint64_t jaydb_commit_fixture_counts(unsigned which) {return which==0?holds:which==1?closes:releases;}
void jaydb_commit_fixture_invalid(unsigned which) {
  if(which==0)sample.abi=2;
  if(which==1)sample.snapshot.abi=2;
  if(which==2)sample.snapshot.monotonic_ns.lo=31;
  if(which==3)sample.peak_flags=0;
}
int jaydb_commit_test_marker(void *out,unsigned op) {
  if(op==1) {++holds;return (int)hold_error;}
  if(op==2) {++releases;return (int)release_error;}
  if(op==4||op==5) {
    if(op==4)++closes;
    if(close_error)return (int)close_error;
    volatile unsigned char *d=out;
    const unsigned char *s=(const unsigned char *)&sample;
    for(size_t n=0;n<sizeof sample;++n)d[n]=s[n];
    if(op==5)((struct jayacct_window_snapshot *)out)->state=JAYACCT_WINDOW_ACTIVE;
    return 0;
  }
  return EINVAL;
}
long jaydb_commit_test_clock(long *ts) {
  ts[0]=(long)(tick/1000000000u);ts[1]=(long)(tick%1000000000u);
  if(clock_signal)raise(clock_signal);
  return 0;
}
