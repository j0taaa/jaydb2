#!/usr/bin/env python3
"""Real private-leaf tests; these C probes are not admitted client programs."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('leaf_native_build', ROOT/'tools/native/build.py')
BUILD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILD)


class LeafTests(unittest.TestCase):
    def execute(self, sources, main, *, memory=False):
        with tempfile.TemporaryDirectory(prefix='jaydb-leaf-test-') as temp:
            folder = Path(temp)
            common = [BUILD.CLANG, '-std=gnu11', '-O2', '-fPIC', '-fvisibility=hidden',
                      '-fno-omit-frame-pointer', '-mno-red-zone', '-fstack-usage', '-fno-builtin',
                      '-I', str(ROOT/'native')]
            objects, reports = [], {}
            for name in sources:
                flags = ['-fsanitize-coverage=trace-pc-guard,bb,no-prune'] if name == 'memory' else []
                obj, ir = folder/(name+'.o'), folder/(name+'.ll')
                subprocess.run([*common, *flags, '-c', str(ROOT/'native'/f'{name}.c'), '-o', str(obj)],
                               check=True, capture_output=True, text=True)
                subprocess.run([*common, *flags, '-S', '-emit-llvm', str(ROOT/'native'/f'{name}.c'), '-o', str(ir)],
                               check=True, capture_output=True, text=True)
                undefined = subprocess.run(['nm', '-u', str(obj)], check=True, capture_output=True, text=True).stdout
                if name == 'memory':
                    self.assertTrue(all(any(symbol in line for symbol in [
                        '__sanitizer_cov_trace_pc_guard', '__start___sancov_guards', '__stop___sancov_guards'])
                        for line in undefined.splitlines()), undefined)
                    BUILD.audit_ir(ir.read_text())
                else:
                    self.assertEqual(undefined.strip(), '')
                frames, dynamic = BUILD._STACK.read_frames((folder/(name+'.su')).read_text())
                self.assertEqual(dynamic, [])
                if name != 'memory':
                    audit = BUILD._STACK.analyze(ir.read_text(), frames, roots=tuple(frames))
                    self.assertTrue(audit['wholeNativeBoundProved'], audit)
                reports[name] = {'frames': frames, 'undefinedSymbols': undefined}
                objects.append(obj)
            source = folder/'main.c'
            source.write_text(main)
            target = folder/'probe'
            subprocess.run([*common, str(source), *map(str, objects), '-pthread', '-ldl', '-o', str(target)],
                           check=True, capture_output=True, text=True)
            result = subprocess.run([str(target)], capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            return reports

    def test_syscall_leafs_real_mapping_growth_clock_and_failure(self):
        self.execute(['leaves'], r'''
#define _GNU_SOURCE
#include "leaves.h"
#include <errno.h>
int main(void) {
  struct timespec before, after;
  if (clock_gettime(CLOCK_MONOTONIC,&before)
      || jaydb_os_clock_gettime(CLOCK_MONOTONIC,&after)) return 1;
  if (after.tv_sec < before.tv_sec || after.tv_sec > before.tv_sec+1) return 2;
  errno=77;
  if (!jaydb_os_clock_gettime(-1,&after) || errno!=77) return 3;
  if (jaydb_os_mmap(0,0,PROT_READ,MAP_PRIVATE|MAP_ANONYMOUS,-1,0)!=MAP_FAILED) return 4;
  unsigned char *p=jaydb_os_mmap(0,4096,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  if (p==MAP_FAILED) return 5;
  p[0]=17; p[4095]=99;
  if (jaydb_os_mprotect(p,4096,PROT_READ) || p[0]!=17) return 6;
  if (jaydb_os_mprotect(p,4096,PROT_READ|PROT_WRITE)) return 7;
  p=jaydb_os_mremap(p,4096,8192,MREMAP_MAYMOVE);
  if (p==MAP_FAILED || p[0]!=17 || p[4095]!=99) return 8;
  p[8191]=23;
  return jaydb_os_munmap(p,8192)!=0;
}
''')

    def test_local_memory_differential_against_libc_including_overlap(self):
        self.execute(['memory'], r'''
#define _GNU_SOURCE
#include <stdint.h>
#include <string.h>
#include <dlfcn.h>
static unsigned polls;
void __sanitizer_cov_trace_pc_guard(uint32_t *p) { (void)p; ++polls; }
void __sanitizer_cov_trace_pc_guard_init(uint32_t *a,uint32_t *b) { while(a<b) *a++=1; }
static uint32_t state=0x915724f3;
static uint32_t next(void) { state^=state<<13; state^=state>>17; return state^=state<<5; }
int main(void) {
  void *lib=dlopen("libc.so.6",RTLD_NOW|RTLD_LOCAL);
  if (!lib) return 1;
  void *(*ref_move)(void*,const void*,size_t)=dlsym(lib,"memmove");
  void *(*ref_copy)(void*,const void*,size_t)=dlsym(lib,"memcpy");
  void *(*ref_set)(void*,int,size_t)=dlsym(lib,"memset");
  int (*ref_compare)(const void*,const void*,size_t)=dlsym(lib,"memcmp");
  size_t (*ref_length)(const char*)=dlsym(lib,"strlen");
  char *(*ref_character)(const char*,int)=dlsym(lib,"strchr");
  unsigned char actual[1024], expected[1024], original[1024];
  for (unsigned run=0;run<2048;++run) {
    for (unsigned i=0;i<1024;++i) actual[i]=expected[i]=original[i]=(unsigned char)next();
    size_t n=next()%513, from=next()%257, to=next()%257;
    memmove(actual+to,actual+from,n); ref_move(expected+to,expected+from,n);
    if (ref_compare(actual,expected,1024)) return 2;
    memcpy(actual+to,original+from,n); ref_copy(expected+to,original+from,n);
    if (ref_compare(actual,expected,1024)) return 3;
    int value=(int)next();
    memset(actual+to,value,n); ref_set(expected+to,value,n);
    if (ref_compare(actual,expected,1024)) return 4;
    int a=memcmp(actual,original,n), b=ref_compare(actual,original,n);
    if ((a>0)!=(b>0) || (a<0)!=(b<0)) return 5;
    actual[1023]=0;
    if (strlen((char*)actual)!=ref_length((char*)actual)) return 6;
    if (strchr((char*)actual,value)!=ref_character((char*)actual,value)) return 7;
  }
  if (polls<2048) return 8;
  return dlclose(lib)!=0;
}
''', memory=True)

    def test_owner_is_allocation_free_and_invisible_to_other_host_thread(self):
        self.execute(['owner'], r'''
#include "owner.h"
#include <pthread.h>
#include <stdatomic.h>
struct jaydb_guard { int sentinel; };
static _Atomic int phase;
static struct jaydb_guard main_guard={17};
static void *other(void *unused) {
  (void)unused;
  while (!atomic_load(&phase)) {}
  for (unsigned i=0;i<10000;++i) if (jaydb_owner_get()) return (void*)1;
  atomic_store(&phase,2);
  while (atomic_load(&phase)!=3) {}
  struct jaydb_guard own_guard={23};
  jaydb_owner_set(&own_guard);
  if (jaydb_owner_get()!=&own_guard) return (void*)2;
  atomic_store(&phase,4);
  while (atomic_load(&phase)!=5) {}
  jaydb_owner_set(0);
  return 0;
}
int main(void) {
  pthread_t thread; void *result;
  jaydb_owner_set(&main_guard);
  if (pthread_create(&thread,0,other,0)) return 1;
  atomic_store(&phase,1);
  while (atomic_load(&phase)!=2) if (jaydb_owner_get()!=&main_guard) return 2;
  jaydb_owner_set(0);
  atomic_store(&phase,3);
  while (atomic_load(&phase)!=4) {}
  for (unsigned i=0;i<10000;++i) if (jaydb_owner_get()) return 3;
  atomic_store(&phase,5);
  if (pthread_join(thread,&result)) return 4;
  return result!=0;
}
''')


if __name__ == '__main__':
    unittest.main(verbosity=2)
