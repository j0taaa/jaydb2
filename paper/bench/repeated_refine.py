#!/usr/bin/env python3
"""Research-only rejection/immutable-fd/flags diagnostics; hold lock + fixed clock.
Run repeated_diagnose.py and repeated_replay.py first.
"""
import subprocess,json,os,fcntl,sys,hashlib,statistics,time,resource
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'.build/paper-bench/repeated';host=root/'.build/paper-bench/repeated-host/target/release/repeated-host';worker=next((p/'artifacts-1105').glob('request*/*.program'));auth=next((p/'artifacts-1105/authenticate').glob('*.program'))
sys.path.insert(0,str(root))
from tools.client import encode,prepared_frame,unframe,decode
from paper.bench.frequency import observe
out=dict(frequency=observe(),harness_sha256=hashlib.sha256(host.read_bytes()).hexdigest(),records=[],matrix=[],memfd={})
def bench(mode,exe,inp,n=200,t=1):
 r=json.loads(subprocess.check_output([str(host),mode,str(exe),str(inp),str(n),str(t)]));out['records'].append(r);print(mode,Path(exe).name,Path(inp).name,t,statistics.median(r['samples_ns'])/1e6,flush=True)
def run(exe,b):return subprocess.run([str(exe),'+RTS','--threads','1','--gpu','off','-RTS'],input=b,capture_output=True,check=True).stdout
def split(b):n=int.from_bytes(b[:8],'big');return b[8:8+n],b[8+n:]
def pack(a,b):return len(a).to_bytes(8,'big')+a+b
for mode in ('pool-4096','pool-65536'):
 try:bench(mode,worker,p/'read-1105.worker.in',100)
 except subprocess.CalledProcessError as error:out.setdefault('unavailable',[]).append(dict(mode=mode,returncode=error.returncode))
for exe in (auth,worker):
 bench('read-file',exe,p/'empty',1000);bench('hash-memory',exe,exe,1000)
reg,rest=split((p/'read-10.worker.in').read_bytes());state,body=split(rest)
handle=json.loads((p/'capture.json').read_text())['fixtures'][0]['handle']
cases=[('empty',b''),('unknown-opcode',b'\x07\xff'),('truncated-extension',b'\x07'),('malformed-value',b'\x07\x01\xff'),('over-limit',b'\x07\x01'+bytes(65535))]
for name,cred,h,proof,args,op in [
 ('valid','alice-token',handle,'',['read','k000009'],1),
 ('bad-credential','bad',handle,'',['read','k000009'],1),
 ('empty-credential','',handle,'',['read','k000009'],1),
 ('nonempty-proof','alice-token',handle,'bad',['read','k000009'],1),
 ('bad-credential-and-proof','bad',handle,'bad',['read','k000009'],1),
 ('unknown-handle','alice-token','f'*64,'',['read','k000009'],1),
 ('bad-credential-unknown-handle','bad','f'*64,'',['read','k000009'],1),
 ('malformed-handle','alice-token','?', '',['read','k000009'],1),
 ('invalid-args','alice-token',handle,'',[],1),
 ('invalidate-must-fallback','alice-token',handle,'',None,2)]:
 cases.append((name,prepared_frame(op,h,cred,args,proof)[8:]))
for name,b in cases:
 a=run(auth,pack(state,b));w=run(worker,pack(reg,pack(state,b)))
 item=dict(case=name,auth_tag=a[0],worker_tag=w[0],early_equal=a==w if a[0]==0 else None,
           worker_response=unframe(w[1:]) if w[0]==0 else unframe(split(w[1:])[1]),auth_sha256=hashlib.sha256(a).hexdigest(),worker_sha256=hashlib.sha256(w).hexdigest())
 if a[0]==0:assert a==w,(name,a,w)
 out['matrix'].append(item)
print('matrix checked',len(cases),flush=True)
for count in (10,1105):
 registry,packet=split((p/f'read-{count}.worker.in').read_bytes());root_bytes,_=split(packet)
 for label,credential,args in [('auth-fail','bad',['read',f'k{count-1:06d}']),('refusal','alice-token',[])]:
  inp=p/f'{label}-{count}.worker.in';inp.write_bytes(pack(registry,pack(root_bytes,prepared_frame(1,handle,credential,args)[8:])))
  bench('capture',worker,inp,100)

# Sealed ELF via actual fd exec (CPython uses fexecve/execveat), with no artifact directory dependency.
fd=os.memfd_create('jaydb-fexecve',os.MFD_ALLOW_SEALING|os.MFD_CLOEXEC);os.write(fd,worker.read_bytes());os.fchmod(fd,0o700)
seals=fcntl.F_SEAL_WRITE|fcntl.F_SEAL_GROW|fcntl.F_SEAL_SHRINK|fcntl.F_SEAL_SEAL;fcntl.fcntl(fd,fcntl.F_ADD_SEALS,seals)
errors={}
for name,fn in [('write',lambda:os.write(fd,b'x')),('grow',lambda:os.ftruncate(fd,worker.stat().st_size+1)),('shrink',lambda:os.ftruncate(fd,0)),('add-seal',lambda:fcntl.fcntl(fd,fcntl.F_ADD_SEALS,fcntl.F_SEAL_WRITE))]:
 try:fn();errors[name]='unexpected success'
 except OSError as e:errors[name]=e.errno
out['root_checks']=[]
for count in (10,1105):
 for op in ('read','update'):
  b=(p/f'{op}-{count}.worker.in').read_bytes();_,rest=split(b);rb,_=split(rest);expected_root=decode(rb)
  if op=='update':expected_root['tables'][0]['rows'][-1]['value']=1
  got=run(worker,b);assert got[0]==1;actual_root,response=split(got[1:]);assert decode(actual_root)==expected_root
  out['root_checks'].append(dict(rows=count,operation=op,exact_state_equal=True))
expected=run(worker,(p/'read-10.worker.in').read_bytes());(p/'fd.in').write_bytes((p/'read-10.worker.in').read_bytes())
with (p/'fd.in').open('rb') as i,(p/'fd.out').open('wb') as o:
 pid=os.fork()
 if pid==0:
  os.dup2(i.fileno(),0);os.dup2(o.fileno(),1);os.chdir('/tmp');os.execve(fd,['sealed-worker','+RTS','--threads','1','--gpu','off','-RTS'],dict(os.environ,BENDRTS=''))
 assert os.waitpid(pid,0)[1]==0
assert (p/'fd.out').read_bytes()==expected
out['memfd']=dict(seals=fcntl.fcntl(fd,fcntl.F_GET_SEALS),expected_seals=seals,mutation_errno=errors,fd_exec_exact_output=True);os.close(fd)
# Identical already-checked literal C, different native compiler flags only.
for flags,label in [(['-O3'],'O3'),(['-O2','-static'],'static')]:
 exe=p/f'{label}.program';subprocess.run(['clang-19','-std=gnu11',*flags,'-w','--no-default-config',str(worker.parent/'checked.c'),'-o',str(exe),'-lm','-pthread'],check=True)
 assert run(exe,(p/'read-10.worker.in').read_bytes())==expected
 if label=='static':bench('hash',exe,p/'empty',1000)
 for count in (10,1105):
  assert run(exe,(p/f'read-{count}.worker.in').read_bytes())==run(worker,(p/f'read-{count}.worker.in').read_bytes())
  bench('capture',exe,p/f'read-{count}.worker.in',100)
subprocess.run(['clang-19','-O2','-static',str(p/'hello.c'),'-o',str(p/'hello-static')],check=True)
bench('capture',p/'hello-static',p/'empty',300)
# Default worker count: prove how many OS threads are actually created.
for exe,inp in [(worker,p/'read-1105.worker.in'),(auth,p/'read-1105.auth.in'),(p/'hello',p/'empty')]:
 subprocess.run(['strace','-f','-ttt','-T','-yy','-e','trace=process,memory,read,write,openat,access','-o',str(p/f'{exe.name[:8]}.default.syscalls.txt'),str(host),'capture',str(exe),str(inp),'2','16'],stdout=subprocess.DEVNULL,check=True)
subprocess.run(['strace','-f','-ttt','-T','-e','execve,execveat','-o',str(p/'memfd-exec.syscalls.txt'),str(host),'memfd',str(worker),str(p/'read-10.worker.in'),'2','1'],stdout=subprocess.DEVNULL,check=True)
# One memory/fault observation per native process, not a latency sample.
out['memory_probes']=[]
for name,exe in [('worker',worker),('auth',auth)]:
 before=resource.getrusage(resource.RUSAGE_CHILDREN)
 child=subprocess.Popen([str(exe),'+RTS','--threads','1','--gpu','off','-RTS'],stdin=subprocess.PIPE,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
 try:
  deadline=time.monotonic()+10
  while 'pipe_read' not in Path(f'/proc/{child.pid}/wchan').read_text():
   if child.poll() is not None:raise RuntimeError('memory probe exited early')
   if time.monotonic()>deadline:raise TimeoutError('memory probe readiness')
   time.sleep(.001)
  status={line.split(':',1)[0]:line.split(':',1)[1].strip() for line in Path(f'/proc/{child.pid}/status').read_text().splitlines() if ':' in line}
  minor_before_input=int(Path(f'/proc/{child.pid}/stat').read_text().split()[9])
  _,err=child.communicate(input=(p/f'read-1105.{name}.in').read_bytes(),timeout=10);assert child.returncode==0,err
  after=resource.getrusage(resource.RUSAGE_CHILDREN)
  out['memory_probes'].append(dict(process=name,ready_vm_size=status['VmSize'],ready_vm_rss=status['VmRSS'],minor_faults_before_input=minor_before_input,total_child_minor_faults=after.ru_minflt-before.ru_minflt,major_faults=after.ru_majflt-before.ru_majflt,stdout_sink='/dev/null; not a latency sample'))
 finally:
  if child.poll() is None:child.kill();child.wait()
(p/'tsc.c').write_text('#include <x86intrin.h>\n#include <time.h>\n#include <stdio.h>\nint main(void){struct timespec a,b,p={0,50000000};clock_gettime(CLOCK_MONOTONIC_RAW,&a);_mm_lfence();unsigned long long x=__rdtsc();nanosleep(&p,0);_mm_lfence();unsigned long long y=__rdtsc();clock_gettime(CLOCK_MONOTONIC_RAW,&b);long long ns=(b.tv_sec-a.tv_sec)*1000000000LL+b.tv_nsec-a.tv_nsec;printf("{\\"cycles\\":%llu,\\"ns\\":%lld}\\n",y-x,ns);return 0;}\n')
subprocess.run(['clang-19','-O2',str(p/'tsc.c'),'-o',str(p/'tsc')],check=True)
out['tsc_calibration']=[json.loads(subprocess.check_output([str(p/'tsc')])) for _ in range(3)]
(p/'refine.json').write_text(json.dumps(out,indent=2)+'\n')
