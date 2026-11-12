#!/usr/bin/env python3
"""Research-only diagnostics. Caller holds the common heavy lock and fixed clock.

Run repeated_diagnose.py first, then build repeated-host (see the report).
Writes diagnostic artifacts under .build/paper-bench/repeated.
"""
import sys,json,subprocess,os,statistics,hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'.build/paper-bench/repeated';host=root/'.build/paper-bench/repeated-host/target/release/repeated-host'
sys.path.insert(0,str(root))
from tools.client import unframe,decode
from paper.bench.frequency import observe

# Scratch build only: no change to the production Cargo package or emitted C.
build=root/'.build/paper-bench/repeated-host';build.mkdir(parents=True,exist_ok=True)
(build/'Cargo.toml').write_text('[package]\nname="repeated-host"\nversion="0.0.0"\nedition="2024"\n[[bin]]\nname="repeated-host"\npath="'+str(root/'paper/bench/repeated-host.rs')+'"\n[dependencies]\nsha2="=0.10.9"\nserde_json="=1.0.154"\nlibc="=0.2.191"\n')
subprocess.run(['cargo','build','--release','--offline','--manifest-path',str(build/'Cargo.toml')],check=True)
(p/'hello.c').write_text('#include <unistd.h>\nint main(void){return write(1,"hello\\n",6)!=6;}\n')
(p/'echo.c').write_text('#include <unistd.h>\nint main(void){char b[8192];ssize_t n;while((n=read(0,b,sizeof(b)))>0){ssize_t i=0;while(i<n){ssize_t r=write(1,b+i,n-i);if(r<0)return 1;i+=r;}}return n<0;}\n')
for name in ('hello','echo'):
 subprocess.run(['clang-19','-O2',str(p/(name+'.c')),'-o',str(p/name)],check=True)

x=json.loads((p/'capture.json').read_text());out=dict(frequency=observe(),records=[],checks=[])
worker=next((p/'artifacts-1105').glob('request*/*.program'));auth=next((p/'artifacts-1105/authenticate').glob('*.program'))
for exe in (worker,auth):
 receipt=json.loads(Path(str(exe)+'.json').read_text());assert hashlib.sha256(exe.read_bytes()).hexdigest()==receipt['executableSha256']
 admitted=json.loads((exe.parent/'checked.c.json').read_text());assert admitted['admission']['primary'] and admitted['admission']['bendtt']
 assert hashlib.sha256((exe.parent/'checked.c').read_bytes()).hexdigest()==admitted['cSha256']
def bench(mode,exe,inp,n=100,threads=1):
 r=json.loads(subprocess.check_output([str(host),mode,str(exe),str(inp),str(n),str(threads)]));out['records'].append(r);(p/'replay.json').write_text(json.dumps(out,indent=2)+'\n');print(mode,Path(exe).name,str(inp),threads,round(statistics.median(r['samples_ns'])/1e6,5),flush=True);return r
(p/'empty').write_bytes(b'')
for exe in (p/'hello',p/'echo'):
 bench('capture',exe,p/'empty',300)
for count in (10,1105):
 for op in ('read','update'):
  for name,exe in (('auth',auth),('worker',worker)):
   inp=p/f'{op}-{count}.{name}.in';b=inp.read_bytes();r=subprocess.run([str(exe),'+RTS','--threads','1','--gpu','off','-RTS'],input=b,capture_output=True,check=True)
   if name=='worker':
    assert r.stdout[0]==1,r.stdout[:100];length=int.from_bytes(r.stdout[1:9],'big');v=unframe(r.stdout[9+length:]);assert v==dict(status='success',value=True if op=='update' else 0),v
    reglen=int.from_bytes(b[:8],'big');off=8+reglen;rootlen=int.from_bytes(b[off:off+8],'big');expected_root=decode(b[off+8:off+8+rootlen])
    if op=='update':expected_root['tables'][0]['rows'][-1]['value']=1
    assert decode(r.stdout[9:9+length])==expected_root
    out['checks'].append(dict(rows=count,op=op,input_bytes=len(b),output_bytes=len(r.stdout),response=v))
   bench('capture',exe,inp)
   bench('pool',exe,inp)
   if op=='read':bench('capture',exe,inp,30,16)
  if op=='read':bench('memfd',worker,p/f'{op}-{count}.worker.in')
for exe in (auth,worker):bench('hash',exe,p/'empty',1000)
a=p/'artifacts-1105';public=a/'public';runtime=a/'runtime';req=next(a.glob('request*'))
bench('seal',req,public,200);bench('seal',runtime,public,200)
for size in (1000,65536,262144):
 (p/'echo.in').write_bytes(bytes(size));bench('capture',p/'echo',p/'echo.in',200)
out['frequency_end']=observe();(p/'replay.json').write_text(json.dumps(out,indent=2)+'\n')
