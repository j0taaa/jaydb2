#!/usr/bin/env python3
"""Real admitted prepared requests. Run under the shared heavy flock."""
import argparse,collections,hashlib,json,os,pathlib,platform,resource,select,signal,statistics,subprocess,sys,time
from datetime import datetime,timezone
ROOT=pathlib.Path(__file__).resolve().parents[3]
SUITE=pathlib.Path(__file__).resolve().parent
OUT=pathlib.Path(os.environ.get("JAYDB_INDEX_BENCH_OUTPUT",str(ROOT/"build/library/index-benchmark-run"))).resolve()
OUT.mkdir(parents=True,exist_ok=True)
STAGE=OUT/'stage'
sys.path.insert(0,str(ROOT))
from tools.client import prepared_frame,unframe,encode
TOKEN='benchmark-token'

def sha(b):return hashlib.sha256(b).hexdigest()
def key(i):return f'k{i:04}'
def email(i):return f'e{i:04}'
def group(i):return f'g{i%8:02}'
def composite(parts):return ''.join('p'+''.join('c'+c for c in part)+'e' for part in parts)+'z'
def summary(samples):
 med=statistics.median(samples)
 return dict(n=len(samples),median_ms=med/1e6,mad_ms=statistics.median(abs(x-med) for x in samples)/1e6,min_ms=min(samples)/1e6,max_ms=max(samples)/1e6,samples_ns=samples)

class Session:
 def __init__(self,kind,tag,result):
  self.kind,self.tag,self.result=kind,tag,result
  self.model={}
  self.log=(OUT/f'{tag}-{kind}.log').open('wb')
  self.p=subprocess.Popen([str(ROOT/'target/release/jaydb2'),'--configuration',str(STAGE/'Configuration.bend'),'--seed',str(STAGE/'Seed.bend'),'--threads','1'],cwd=ROOT,env=dict(os.environ,BENDRTS='',TMPDIR=str(OUT/'tmp')),stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=self.log,start_new_session=True)
  self.handle=None
  source=(STAGE/'Client.bend').read_text();proof=(STAGE/'ClientProof.bend').read_text()
  t=time.perf_counter_ns()
  try:
   reply=self.exchange(prepared_frame(0,source,TOKEN,None,proof))
   assert reply['status']=='prepared',reply
   self.handle=reply['value']
  except BaseException:
   if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait()
   self.p.stdin.close();self.p.stdout.close();self.log.close()
   raise
  result['preparation'].append(dict(tag=tag,kind=kind,elapsed_ns=time.perf_counter_ns()-t))
 def read(self,n):
  buf=bytearray()
  while len(buf)<n:
   if not select.select([self.p.stdout],[],[],180)[0]:raise RuntimeError('response timed out: '+str(self.log.name))
   b=os.read(self.p.stdout.fileno(),n-len(buf))
   if not b:raise RuntimeError('host exited: '+str(self.log.name))
   buf.extend(b)
  return bytes(buf)
 def exchange(self,message):
  self.p.stdin.write(message);self.p.stdin.flush()
  h=self.read(8);body=self.read(int.from_bytes(h,'big'))
  return unframe(h+body)
 def call(self,args,expected,phase='validation',case=None):
  message=prepared_frame(1,self.handle,TOKEN,args)
  t=time.perf_counter_ns();actual=self.exchange(message);elapsed=time.perf_counter_ns()-t
  want=dict(status='success',value=expected)
  rec=dict(tag=self.tag,kind=self.kind,phase=phase,case=case,args=args,elapsed_ns=elapsed,actual=actual,expected=want,checked=actual==want)
  with (OUT/'requests.jsonl').open('a') as f:f.write(json.dumps(rec,separators=(',',':'))+'\n')
  self.result['checked_requests']+=1
  assert actual==want,(rec,self.log.name)
  return elapsed
 def put(self,i,em,gr,pad,phase='setup'):
  k=key(i);old=self.model.get(k,dict(email='',group=''))
  ns=self.call(['put',self.kind,k,em,gr,pad,old['email'],old['group']],k,phase,'update' if phase in ('sample','warmup') else 'fill')
  self.model[k]=dict(id=k,email=em,group=gr,pad=pad)
  return ns
 def verify(self,i):
  k=key(i);r=self.model[k]
  for field in ('email','group','pad'):self.call(['probe','base',k,field],r[field])
  if self.kind=='unique':
   self.call(['probe','unique_index',composite([r['email']]),'target'],k)
   self.call(['probe','unique_index',composite([r['email']]),'value'],composite([r['email']]))
  if self.kind=='many':
   self.call(['probe','many_index',composite([r['group'],k]),'target'],k)
   self.call(['probe','many_index',composite([r['group'],k]),'value'],composite([r['group']]))
 def state(self):
  base=list(self.model.values());mi=[];ui=[]
  for r in base:
   parts=[r['group']] if self.kind=='many' else [r['email']]
   ik=composite(parts+[r['id']]) if self.kind=='many' else composite(parts)
   entry=dict(id=ik,target=r['id'],value=composite(parts))
   if self.kind=='many':mi.append(entry)
   if self.kind=='unique':ui.append(entry)
  return dict(tables=[dict(name='base',rows=base),dict(name='many_index',rows=sorted(mi,key=lambda r:r['id'])),dict(name='unique_index',rows=sorted(ui,key=lambda r:r['id']))],users=[dict(credential=TOKEN,id='bench',kind='user')])
 def close(self):
  try:
   self.p.stdin.close();rc=self.p.wait(timeout=30)
   if rc:raise RuntimeError((rc,self.log.name))
  finally:
   if self.p.poll() is None:os.killpg(self.p.pid,signal.SIGKILL);self.p.wait()
   self.p.stdout.close()
   self.log.close()

def run_case(n,padbytes,options,result):
 tag=f'rows-{n}-pad-{padbytes}';sessions=[]
 try:
  for kind in ('none','unique','many'):
   s=Session(kind,tag,result);sessions.append(s)
   for i in range(n):s.put(i,email(i),group(i),'p'*padbytes)
   for i in range(n):s.verify(i)
   bs=encode(s.state())
   result['states'].append(dict(tag=tag,kind=kind,rows=n,padding_bytes=padbytes,canonical_bytes=len(bs),model_sha256=sha(bs)))
   print(f'{tag} {kind}: prepared, filled and every row checked; {len(bs)} state bytes',flush=True)
  bare,unique,many=sessions
  # Same ordered result: unique find may stop on first hit; many scans return all matches.
  cases=[('unique-first','find',email(0),[key(0)],unique,'unique'),('unique-middle','find',email(n//2),[key(n//2)],unique,'unique'),('unique-last','find',email(n-1),[key(n-1)],unique,'unique'),('unique-miss','find','missing',[],unique,'unique'),('nonunique-match','scan','g00',[key(i) for i in range(n) if i%8==0],many,'many'),('nonunique-miss','scan','g99',[],many,'many')]
  for name,scan,query,want,indexed,idxcmd in cases:
   variants=[('base_without_index',bare,scan),('base_with_index',indexed,scan),('indexed_lookup',indexed,idxcmd)]
   samples=collections.defaultdict(list)
   for j in range(options.warmups+options.samples):
    # Rotate + alternate variant order. Preparation and Python encoding are outside timing.
    seq=variants[j%3:]+variants[:j%3]
    if j%2:seq=list(reversed(seq))
    phase='warmup' if j<options.warmups else 'sample'
    for label,s,cmd in seq:
     elapsed=s.call([cmd,query],want,phase,name)
     if phase=='sample':samples[label].append(elapsed)
   result['measurements'].append(dict(tag=tag,rows=n,padding_bytes=padbytes,case=name,query=query,matches=len(want),results={k:summary(v) for k,v in samples.items()}))
   print(tag,name,{k:round(statistics.median(v)/1e6,3) for k,v in samples.items()},flush=True)
   save(result)
  # Change indexed fields, rather than timing a no-op or an unrelated field.
  samples=collections.defaultdict(list)
  for j in range(options.warmups+options.samples):
   phase='warmup' if j<options.warmups else 'sample'
   order=sessions[j%3:]+sessions[:j%3]
   if j%2:order=list(reversed(order))
   for s in order:
    em=('x' if j%2==0 else 'e')+f'{n-1:04}'
    gr=f'g{((n-1)%8+(1 if j%2==0 else 0))%8:02}'
    old=dict(s.model[key(n-1)])
    elapsed=s.put(n-1,em,gr,'p'*padbytes,phase)
    if phase=='sample':samples[s.kind].append(elapsed)
    s.verify(n-1)
    if s.kind=='unique' and old['email']!=em:s.call(['probe','unique_index',composite([old['email']]),'target'],None)
    if s.kind=='many' and old['group']!=gr:s.call(['probe','many_index',composite([old['group'],key(n-1)]),'target'],None)
    # Equality query result includes every matching item, not merely a row count.
    if s.kind=='many':s.call(['many',gr],[k for k,r in s.model.items() if r['group']==gr])
   save(result)
  result['writes'].append(dict(tag=tag,rows=n,padding_bytes=padbytes,results={k:summary(v) for k,v in samples.items()}))
  print(tag,'maintained update',{k:round(statistics.median(v)/1e6,3) for k,v in samples.items()},flush=True)
 finally:
  for s in sessions:s.close()

def save(result):
 (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')

def main():
 p=argparse.ArgumentParser();p.add_argument('--rows',nargs='+',type=int,default=[8,64,256]);p.add_argument('--samples',type=int,default=9);p.add_argument('--warmups',type=int,default=2);p.add_argument('--wide',action='store_true');options=p.parse_args()
 if options.samples<=0 or options.warmups<0 or any(n<8 for n in options.rows):p.error("rows must be >=8; samples positive; warmups nonnegative")
 _,hard=resource.getrlimit(resource.RLIMIT_STACK);resource.setrlimit(resource.RLIMIT_STACK,(hard,hard))
 result=dict(status='running',started_utc=datetime.now(timezone.utc).isoformat(),root=str(ROOT),head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),binary_sha256=sha((ROOT/'target/release/jaydb2').read_bytes()),toolchain_lock=json.loads((ROOT/'tools/admission/toolchain.lock.json').read_text()),hardware=dict(platform=platform.platform(),cpu=next(l.split(':',1)[1].strip() for l in pathlib.Path('/proc/cpuinfo').read_text().splitlines() if l.startswith('model name')),logical_cpus=os.cpu_count(),affinity=sorted(os.sched_getaffinity(0))),settings=dict(samples=options.samples,warmups=options.warmups,native_threads=1,gpu='off',BENDRTS='',persistence=False,timing='complete prepared request, preencoded frame write through complete response bytes; verification outside interval',ordering='rotated and alternating variants every round',policy='explicit zero-law benchmark config; normal structure/size validation and official proof/admission retained; index projection checked by external model, not a performance claim for arbitrary administrator laws'),sources_sha256={str(p.relative_to(STAGE)):sha(p.read_bytes()) for p in STAGE.glob('*.bend')},measurements=[],writes=[],states=[],preparation=[],checked_requests=0)
 result['working_tree']=subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True)
 result['tracked_patch_sha256']=sha(subprocess.check_output(['git','diff','HEAD','--binary'],cwd=ROOT))
 result['suite_sha256']={p.name:sha(p.read_bytes()) for p in SUITE.iterdir() if p.is_file() and p.suffix in ('.py','.sh','.bend')}
 save(result)
 try:
  for n in options.rows:run_case(n,128,options,result)
  if options.wide:run_case(64,2048,options,result)
  result['status']='passed';result['finished_utc']=datetime.now(timezone.utc).isoformat();save(result)
 except Exception as e:
  result['status']='failed';result['error']=repr(e);save(result);raise
 print('PASS',result['checked_requests'],'checked actual prepared requests',flush=True)
if __name__=='__main__':main()
