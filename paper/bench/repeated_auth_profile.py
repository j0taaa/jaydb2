#!/usr/bin/env python3
"""Research authentication-region probes; caller holds heavy lock + fixed clock.

Extracts post-authentication continuation symbols from the actual literal C.
Worker measures Gate.begin authentication; auth measures Input authentication.
"""
import subprocess,time,json,re
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'.build/paper-bench/repeated';host=root/'.build/paper-bench/repeated-host/target/release/repeated-host'
for name,exe,case,callback in [('worker',next((p/'artifacts-1105').glob('request*/*.program')),'Gate_begin','Gate_begin'),('auth',next((p/'artifacts-1105/authenticate').glob('*.program')),'Input_authenticate_pre','Input_authenticate_pre')]:
 c=(exe.parent/'checked.c').read_text();part=c.split('WL_CASE(FID_'+case+')',1)[1].split('#endif',1)[0];symbol='WL_'+re.search(r'FID_'+callback+r'_k\d+',part)[0]
 bt=f'''BEGIN {{ printf("READY\\n"); }}
uprobe:{exe}:main {{ printf("start %d 0\\n",pid); }}
uprobe:{exe}:WL_FID_Data_authenticate {{ @call[tid]=nsecs; }}
uprobe:{exe}:{symbol} {{ printf("credential_check %d %llu\\n",pid,nsecs-@call[tid]); }}
END {{ clear(@call); }}
'''
 script=p/f'{name}-authonly.bt';script.write_text(bt)
 for rows in (10,1105):
  trace=p/f'read-{rows}.{name}.authonly.bpf.txt'
  with trace.open('w') as o:
   tracer=subprocess.Popen(['sudo','-n','bpftrace','-B','line',str(script)],stdout=o)
   try:
    deadline=time.monotonic()+30
    while 'READY' not in trace.read_text():
     if tracer.poll() is not None:raise RuntimeError('tracer exited')
     if time.monotonic()>deadline:raise TimeoutError('ready')
     time.sleep(.02)
    subprocess.run([str(host),'capture',str(exe),str(p/f'read-{rows}.{name}.in'),'30','1'],stdout=subprocess.DEVNULL,check=True)
    time.sleep(.1)
   finally:
    subprocess.run(['sudo','-n','kill','-INT',str(tracer.pid)],check=True);tracer.wait(timeout=20)
  assert 'credential_check' in trace.read_text()
  print(name,rows,symbol,flush=True)
