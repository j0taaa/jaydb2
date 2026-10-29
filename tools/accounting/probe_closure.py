"""Exercise the selected runtime closure, recording evidence, never certification.

Ptrace and strace run separately, because two ptracers cannot own one tracee.
Only this worker's .build directory and CLOSURE_RESULTS.json are written.
"""
from __future__ import annotations
import json
from pathlib import Path
import re
import subprocess
import sys

from .build import build, ROOT, DEFAULT_OUTPUT
from .inventory import digest

SYSCALLS=('mmap,mprotect,munmap,mremap,brk,madvise,pkey_mprotect,remap_file_pages,'
          'fork,vfork,clone,clone3,execve,execveat,exit,exit_group,'
          'io_uring_setup,io_uring_register,io_uring_enter,shmget,shmat,shmdt,shmctl,'
          'memfd_create,memfd_secret,ftruncate,fallocate,ioctl,recvmsg,sendmsg,pidfd_getfd,unshare')


def main():
    library,tracer=build()
    out=DEFAULT_OUTPUT
    source=out/'closure-minimal.bendtt'
    source.write_text('unit : <ok> = .ok\n')
    pin=json.loads((ROOT/'tools/verifier/verifier.lock.json').read_text())
    kernel=ROOT/f'.tools/build/verifier-{pin["sourceSha256"]}/bendtt-budget'
    if digest(kernel)!=pin['kernelSha256']:raise RuntimeError('Verifier binary pin changed')
    commands={
        'python_host':[sys.executable,'-B','-c',
                       'import tools.service.controller,tools.service.staging,tools.service.abi; '
                       f'from tools.accounting.client import Library; Library({str(library)!r}); print("host_imports_loaded")'],
        'node_pipeline':[sys.executable,'-B','tools/admission/run.py','--memory-bytes','536870912','--',
                         'node','tests/admission/resource_probe.mjs','deep'],
        'bendtt':[str(kernel),str(source),'400000000'],
        'clang_link':['/usr/bin/clang-19','-O2','-pthread','-fPIC','-shared',
                      'native/accounting/counter.c','-o',str(out/'closure-counter.so')],
    }
    artifacts={str(p):digest(p) for p in (tracer,library,kernel,Path('/usr/bin/clang-19').resolve(),Path('/usr/bin/ld').resolve())}
    results=[]
    for name,command in commands.items():
        report=out/f'closure-{name}.jsonl'
        run=subprocess.run([str(tracer),'--report',str(report),'--',*command],cwd=ROOT,
                           capture_output=True,text=True,timeout=45)
        rows=[json.loads(s) for s in report.read_text().splitlines()]
        if run.returncode or rows[-1].get('type')!='summary':
            raise RuntimeError(f'{name} observation failed: {run.returncode}: {run.stderr}')
        summary=rows[-1]
        witness=next(r for r in rows if r.get('type')=='snapshot' and r['sequence']==summary['peak_sequence'])
        if witness['current']!=summary['peak'] or witness['time_ns']!=summary['peak_time_ns']:
            raise AssertionError('Historical peak provenance changed')
        trace=out/f'closure-{name}.strace'
        traced=subprocess.run(['strace','-f','-qq','-o',str(trace),'-e','trace='+SYSCALLS,*command],
                              cwd=ROOT,capture_output=True,text=True,timeout=45)
        if traced.returncode:raise RuntimeError(f'{name} syscall probe failed: {traced.stderr}')
        counts={}
        for line in trace.read_text().splitlines():
            m=re.match(r'\d+\s+([a-z0-9_]+)\(',line)
            if m:counts[m[1]]=counts.get(m[1],0)+1
        results.append({'name':name,'command':command,'status':run.returncode,'stdout':run.stdout,
                        'summary':summary,'peak_witness':witness,
                        'syscall_counts':dict(sorted(counts.items())),
                        'report':str(report.relative_to(ROOT)),'report_sha256':digest(report),
                        'strace':str(trace.relative_to(ROOT)),'strace_sha256':digest(trace)})
    for p,expected in artifacts.items():
        if digest(p)!=expected:raise RuntimeError(f'Artifact changed during closure probes: {p}')
    result={'format':'jaydb-accounting-closure-probes-v1','complete_measurement':False,
            'meaning':'Evidence for these executions; absence in a trace is not proof of unreachable APIs.',
            'artifact_hashes':artifacts,'results':results}
    (ROOT/'tests/accounting/CLOSURE_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({r['name']:{'peak':r['summary']['peak'],'uring_objects':r['summary']['uring_objects_created'],
                     'unsupported_object_events':r['summary']['unsupported_object_events']} for r in results},indent=2))


if __name__=='__main__':main()
