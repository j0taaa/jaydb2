#!/usr/bin/env python3
"""Research-only diagnostics. Caller holds the common heavy lock and fixed clock.

Run repeated_diagnose.py first, then build repeated-host (see the report).
Writes diagnostic artifacts under .build/paper-bench/repeated.
"""
import subprocess,json,os,hashlib,time,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'.build/paper-bench/repeated';host=root/'.build/paper-bench/repeated-host/target/release/repeated-host';worker=next((p/'artifacts-1105').glob('request*/*.program'));auth=next((p/'artifacts-1105/authenticate').glob('*.program'))
(p/'profile-metadata.json').write_text(json.dumps(dict(harness_sha256=hashlib.sha256(host.read_bytes()).hexdigest(),commands='repeated_profile.py; 30 samples + warmup for BPF/stat/summary, 2 + warmup for detailed strace, 100 + warmup for perf record'),indent=2)+'\n')
base=(root/'paper/bench/repeated-profile.bt.in').read_text()
for name,exe in [('worker',worker),('auth',auth)]:
 text=base.replace('EXE',str(exe))
 if name=='auth':
  text='\n'.join(s for s in text.splitlines() if not any(k in s for k in ('jaydb_loop_run','WL_FID_Core_start','WL_FID_Data_state_value')))+'\n'
  text=text.replace('clear(@loop);','')
 script=p/f'{name}-batch.bt';script.write_text(text)
 for count in (10,1105):
  for op in ('read','update') if name=='worker' else ('read',):
   label=f'{op}-{count}.{name}';args=[str(host),'capture',str(exe),str(p/f'{label}.in'),'30','1']
   # -c restricts uprobes to the launched PID, which would be the harness.
   # Attach globally, wait for BEGIN, then launch our known worker children.
   trace=p/f'{label}.bpf.txt'
   with trace.open('w') as o:
    tracer=subprocess.Popen(['sudo','-n','bpftrace','-B','line',str(script)],stdout=o)
    try:
     deadline=time.monotonic()+30
     while 'READY' not in trace.read_text():
      if tracer.poll() is not None:raise RuntimeError('bpftrace exited before READY')
      if time.monotonic()>deadline:raise TimeoutError('bpftrace READY')
      time.sleep(0.02)
     (p/f'{label}.bpf-host.json').write_bytes(subprocess.check_output(args))
     time.sleep(0.1) # Drain probe records; outside every timed worker call.
    finally:
     subprocess.run(['sudo','-n','kill','-INT',str(tracer.pid)],check=True)
     tracer.wait(timeout=20)
   assert 'runtime_to_loop' in trace.read_text(),'no worker probes recorded'
   if '--bpf-only' in sys.argv:continue
   with (p/f'{label}.stat.txt').open('w') as o:
    subprocess.run(['sudo','-n','perf','stat','-x,','-e','task-clock,cycles,instructions,minor-faults,major-faults,context-switches','--',*args],stdout=subprocess.DEVNULL,stderr=o,check=True)
   with (p/f'{label}.strace-summary.txt').open('w') as o:
    subprocess.run(['strace','-f','-c','--',*args[:6]],stdout=subprocess.DEVNULL,stderr=o,check=True)
   with (p/f'{label}.strace.txt').open('w') as o:
    subprocess.run(['strace','-f','-ttt','-T','-yy','-e','trace=process,memory,read,write,openat,newfstatat,statx,readlink','-o',str(p/f'{label}.syscalls.txt'),*args[:4],'2','1'],stdout=subprocess.DEVNULL,stderr=o,check=True)
   # Symbol self sampling in the exact literal-C -O2 executable, no recompilation.
   if count==1105 or name=='worker':
    subprocess.run(['sudo','-n','perf','record','-q','-e','cycles:u','-F','4999','-o',str(p/f'{label}.perf.data'),'--',*args[:4],'100','1'],stdout=subprocess.DEVNULL,check=True)
    with (p/f'{label}.perf.txt').open('w') as o:
     subprocess.run(['sudo','-n','perf','report','--stdio','--no-children','--percent-limit','0.1','-s','comm,dso,symbol','-i',str(p/f'{label}.perf.data')],stdout=o,check=True)
   print('profiled',label,flush=True)
# Host floor and loader diagnostics.
for exe in [p/'hello',worker,auth]:
 inp=p/'empty' if exe.name=='hello' else p/('read-10.worker.in' if exe==worker else 'read-10.auth.in')
 for i in range(3):
  with (p/f'{exe.parent.name}-{exe.name[:8]}-{i}.loader.txt').open('w') as o:
   subprocess.run([str(exe),'+RTS','--threads','1','--gpu','off','-RTS'],input=inp.read_bytes(),stdout=subprocess.DEVNULL,stderr=o,env={**os.environ,'LD_DEBUG':'statistics','BENDRTS':''},check=True)
