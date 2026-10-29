#!/usr/bin/env python3
"""Isolated exploration, NOT an enabled backend mode or admitted-client test.

Exercise Clang19 preserve_none on actual split frames, then the gold/libgcc
bridge to a separately compiled ordinary C callee. Core dumps are disabled.
"""
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import tempfile


SPLIT = r'''
#define _GNU_SOURCE
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
extern uint64_t ordinary(uint64_t);
static unsigned mixed;
__attribute__((preserve_none, noinline))
static uint64_t segment(uint64_t n, uint64_t *bank, volatile uint8_t *previous,
                        uint64_t a, uint64_t b, uint64_t c, uint64_t d, uint64_t e) {
  volatile uint8_t bytes[80000];
  for (uint64_t i=0; i<sizeof bytes; ++i) bytes[i]=(uint8_t)(i+n);
  if (*bank != 17 || (previous && previous[12345] != (uint8_t)(12345+n+1))) abort();
  uint64_t result = n ? segment(n-1, bank, bytes, a,b,c,d,e) : a+b+c+d+e;
  if (bytes[12345] != (uint8_t)(12345+n) || *bank != 17) abort();
  return result;
}
static void *worker(void *unused) {
  (void)unused;
  uint64_t bank=17;
  uint64_t result=mixed ? ordinary(bank) : segment(8,&bank,0,1,2,3,4,5);
  return (void *)(uintptr_t)(result != (mixed ? 17 : 15));
}
int main(int argc, char **argv) {
  (void)argv;
  mixed=argc>1;
  pthread_attr_t attr;
  pthread_t thread;
  void *result;
  if (pthread_attr_init(&attr) || pthread_attr_setstacksize(&attr,65536)
      || pthread_create(&thread,&attr,worker,0)) return 2;
  if (pthread_attr_destroy(&attr) || pthread_join(thread,&result)) return 3;
  return (int)(uintptr_t)result;
}
'''

ORDINARY = r'''
#include <stdint.h>
__attribute__((noinline)) uint64_t ordinary(uint64_t value) {
  volatile uint8_t bytes[2*1024*1024];
  for (uint64_t i=0; i<sizeof bytes; ++i) bytes[i]=(uint8_t)(i+value);
  return bytes[0];
}
'''


def limits():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def main():
    with tempfile.TemporaryDirectory(prefix='jaydb-split-probe-') as temp:
        folder = Path(temp)
        split, ordinary = folder/'split.c', folder/'ordinary.c'
        split.write_text(SPLIT)
        ordinary.write_text(ORDINARY)
        common = ['/usr/bin/clang-19', '-O2', '-fno-omit-frame-pointer', '-mno-red-zone', '-fstack-usage']
        commands = [common + ['-fsplit-stack', '-c', str(split), '-o', str(folder/'split.o')],
                    common + ['-c', str(ordinary), '-o', str(folder/'ordinary.o')],
                    ['/usr/bin/clang-19', '-fsplit-stack', '-fuse-ld=gold', '-pthread',
                     str(folder/'split.o'), str(folder/'ordinary.o'), '-o', str(folder/'probe')]]
        for command in commands:
            subprocess.run(command, check=True, capture_output=True, text=True, timeout=30, preexec_fn=limits)
        records = []
        for name, args in [('all-split-preserve-none', []), ('external-nonsplit-frame', ['mixed'])]:
            result = subprocess.run([str(folder/'probe'), *args], capture_output=True, text=True,
                                    timeout=10, preexec_fn=limits)
            records.append({'case': name, 'returncode': result.returncode, 'stderr': result.stderr})
        assembly = subprocess.run(['objdump', '-d', str(folder/'probe')], check=True,
                                  capture_output=True, text=True, timeout=10).stdout
        print(json.dumps({'compiler': common[0], 'sourcesSha256': {
              'split': hashlib.sha256(SPLIT.encode()).hexdigest(),
              'ordinary': hashlib.sha256(ORDINARY.encode()).hexdigest()},
              'stackUsage': {'split': (folder/'split.su').read_text(),
                             'ordinary': (folder/'ordinary.su').read_text()},
              'linkedMorestackNonSplit': '<__morestack_non_split>:' in assembly,
              'cases': records, 'backendIntegrated': False}, indent=2))


if __name__ == '__main__':
    main()
