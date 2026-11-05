from pathlib import Path
import argparse,json,statistics,time
import run as bench
SUITE=Path(__file__).resolve().parent
OUT=bench.OUT

def main():
 p=argparse.ArgumentParser();p.add_argument('--rows',type=int,default=256);p.add_argument('--samples',type=int,default=9);p.add_argument('--warmups',type=int,default=2);p.add_argument('--queries',nargs='+',type=int,default=[1,4,16]);opts=p.parse_args()
 assert opts.rows>=8 and opts.samples>0 and opts.warmups>=0 and all(n>0 for n in opts.queries)
 original=json.loads((OUT/'results.json').read_text());assert original['status']=='passed'
 if (OUT/'requests.jsonl').exists() and not (OUT/'single-requests.jsonl').exists():(OUT/'requests.jsonl').rename(OUT/'single-requests.jsonl')
 result={k:original[k] for k in ['root','head','binary_sha256','toolchain_lock','hardware','working_tree','tracked_patch_sha256','suite_sha256']}
 result.update(status='running',rows=opts.rows,padding_bytes=128,samples=opts.samples,warmups=opts.warmups,checked_requests=0,preparation=[],measurements=[],validation='Same unchanged host and public environment as single-query benchmark. Base scan enumerates keys ONCE per batch; every query is a miss, so early exit cannot improve its scans. Positive/negative batch controls compare exact outputs. No persistence. Official universal admission and termination proofs retained.')
 code=(SUITE/'BatchClient.bend').read_text();proof=(SUITE/'BatchProof.bend').read_text()
 result['submitted_sha256']={'code':bench.sha(code.encode()),'proof':bench.sha(proof.encode())}
 sessions=[]
 try:
  for kind in ('none','unique'):
   s=bench.Session(kind,f'batch-rows-{opts.rows}',result);sessions.append(s)
   for i in range(opts.rows):s.put(i,bench.email(i),bench.group(i),'p'*128)
   for i in sorted({0,1,opts.rows//2-1,opts.rows//2,opts.rows-2,opts.rows-1}):s.verify(i)
   t=time.perf_counter_ns();response=s.exchange(bench.prepared_frame(0,code,bench.TOKEN,None,proof));assert response['status']=='prepared',response
   result['preparation'].append(dict(kind=kind,workload='batch',elapsed_ns=time.perf_counter_ns()-t));s.handle=response['value']
   print('batch prepared and filled:',kind,flush=True)
  bare,indexed=sessions
  variants=[('base_without_index',bare,False),('base_with_index',indexed,False),('indexed_lookup',indexed,True)]
  positions=[0,1,opts.rows//4,opts.rows//2-1,opts.rows//2,3*opts.rows//4,opts.rows-2,opts.rows-1]
  hit_queries=[bench.email(i) for i in positions]+['missing-a','missing-b']
  expected=[[bench.key(i)] for i in positions]+[[],[]]
  for label,s,mode in variants:s.call([mode]+hit_queries,expected,case='batch-positive-control')
  for n in opts.queries:
   samples={name:[] for name,_,_ in variants}
   for j in range(opts.warmups+opts.samples):
    seq=variants[j%3:]+variants[:j%3]
    if j%2:seq=list(reversed(seq))
    query=[f'missing-{j:02}-{i:02}' for i in range(n)]
    phase='warmup' if j<opts.warmups else 'sample'
    for label,s,mode in seq:
     elapsed=s.call([mode]+query,[[] for _ in query],phase,case=f'batch-{n}-unique-misses')
     if phase=='sample':samples[label].append(elapsed)
   result['measurements'].append(dict(queries_per_transaction=n,case='unique-misses',results={k:bench.summary(v) for k,v in samples.items()}))
   (OUT/'batch-results.json').write_text(json.dumps(result,indent=2)+'\n')
   print('batch misses',n,{k:round(statistics.median(v)/1e6,3) for k,v in samples.items()},flush=True)
  result['status']='passed'
 finally:
  for s in sessions:s.close()
  (OUT/'batch-results.json').write_text(json.dumps(result,indent=2)+'\n')
  if (OUT/'requests.jsonl').exists():(OUT/'requests.jsonl').rename(OUT/'batch-requests.jsonl')
 print('PASS batch',result['checked_requests'],'checked requests',flush=True)
if __name__=='__main__':main()
