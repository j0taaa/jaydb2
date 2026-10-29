/* Explicit synthetic observations for component tests, never MedicaoReal. */
#define _POSIX_C_SOURCE 200809L
#include "../../tools/service/receiving.h"
#include <signal.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static struct jayacct_window_snapshot current;
static uint64_t next_scope,sequence=1,flags=JAYACCT_FROZEN,global_peak=100;
static int open_error,signal_after_open;
static uint64_t chunk_calls,signal_chunk;
static int signal_after_chunk;
static struct jayacct_u128 timestamp(void) {
  struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);
  __uint128_t n=(__uint128_t)ts.tv_sec*1000000000u+ts.tv_nsec;
  return (struct jayacct_u128){(uint64_t)n,(uint64_t)(n>>64)};
}
static void initialize(void) {
  if(current.abi)return;
  current.abi=1;current.snapshot.abi=1;current.snapshot.sequence.lo=sequence;
  current.snapshot.flags=flags;
}
int jaydb_receiving_test_open(struct jayacct_window_snapshot *out) {
  initialize();
  if(open_error)return open_error;
  if(current.state==JAYACCT_WINDOW_ACTIVE)return EBUSY;
  memset(&current,0,sizeof current);
  current.abi=current.snapshot.abi=1;
  current.state=JAYACCT_WINDOW_ACTIVE;
  current.scope_id.lo=++next_scope;
  current.begin_sequence.lo=current.snapshot.sequence.lo=++sequence;
  current.peak_sequence=current.begin_sequence;
  current.begin_monotonic_ns=current.snapshot.monotonic_ns=timestamp();
  current.peak_monotonic_ns=current.begin_monotonic_ns;
  current.snapshot.current.lo=current.peak.lo=100;
  current.snapshot.peak.lo=global_peak;
  current.snapshot.peak_sequence=current.begin_sequence;
  current.snapshot.peak_monotonic_ns=current.begin_monotonic_ns;
  current.snapshot.peak_flags=current.snapshot.flags=current.peak_flags=flags;
  *out=current;
  if(signal_after_open)kill(getpid(),signal_after_open);
  return 0;
}
void jaydb_receiving_test_read(struct jayacct_window_snapshot *out) {initialize();*out=current;}
void jaydb_receiving_test_close(void) {
  current.state=JAYACCT_WINDOW_CLOSED;
  current.end_sequence=current.snapshot.sequence;
  current.end_monotonic_ns=current.snapshot.monotonic_ns;
}
void jaydb_receiving_test_flags(uint64_t value) {flags=value;}
void jaydb_receiving_test_global_peak(uint64_t value) {global_peak=value;}
void jaydb_receiving_test_error(int value) {open_error=value;}
void jaydb_receiving_test_signal(int value) {signal_after_open=value;}
void jaydb_receiving_test_chunk_signal(uint64_t nth,int value) {
  chunk_calls=0;signal_chunk=nth;signal_after_chunk=value;
}
void jaydb_receiving_test_chunk_completed(void) {
  if(++chunk_calls==signal_chunk && signal_after_chunk)kill(getpid(),signal_after_chunk);
}
void jaydb_receiving_test_peak(uint64_t value) {
  current.snapshot.sequence.lo=++sequence;
  current.snapshot.monotonic_ns=timestamp();
  current.snapshot.current.lo=value;
  if(value>current.peak.lo) {
    current.peak.lo=value;current.peak_sequence=current.snapshot.sequence;
    current.peak_monotonic_ns=current.snapshot.monotonic_ns;
  }
}
