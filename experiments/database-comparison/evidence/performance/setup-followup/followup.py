#!/usr/bin/env python3
"""Independent paired setup diagnostic. Never changes measured benchmark inputs."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import statistics
import subprocess
import sys
import time

CANDIDATE=Path('/home/jota/projects/jaydb2-performance')
BASELINE=Path('/home/jota/projects/jaydb2-performance-baseline')
OUT=CANDIDATE/'build/performance-setup-followup'
CASES=[('01_personal_tasks','reopen_and_client_prepare_ns'),('02_household_budget','create_schema_and_client_ns'),('03_editorial_blog','reopen_and_client_prepare_ns'),('04_ecommerce','create_schema_and_client_ns')]

def now():return datetime.now(timezone.utc).isoformat()
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def original(root):return root/'build'/('performance-baseline' if root==BASELINE else 'performance-candidate')
def storage_hashes(root,scenario):
 p=original(root)/scenario/'jaydb2/storage'
 return {str(f.relative_to(p)):digest(f) for f in p.rglob('*') if f.is_file()}
def save(p,value):
 t=p.with_suffix('.tmp');t.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');t.replace(p)

def worker(options):
 root=Path(options.root)
 sys.path.insert(0,str(root/'experiments/database-comparison'))
 import jay
 from model import load,equal
 from run import identity
 assert jay.ROOT==root,(jay.ROOT,root)
 source_before=identity()
 recorded=json.loads((original(root)/'result.json').read_text())
 binary=Path(recorded['jay_binary'])
 assert digest(binary)==recorded['jay_binary_sha256'],'Frozen binary changed'
 scenario=load(root/'experiments/database-comparison/scenarios'/f'{options.scenario}.json')
 original_folder=original(root)/options.scenario/'jaydb2'
 original_before=storage_hashes(root,options.scenario)
 folder=Path(options.folder);folder.mkdir(parents=True,exist_ok=False)
 tmp=folder/'tmp';tmp.mkdir()
 resource.setrlimit(resource.RLIMIT_STACK,(resource.RLIM_INFINITY,resource.getrlimit(resource.RLIMIT_STACK)[1]))
 env=dict(os.environ,BEND_NO_TELEMETRY='1',BENDRTS='',TMPDIR=str(tmp),CARGO_TARGET_DIR=str(root/'build/database-comparison-target'))
 output={'engine_variant':options.variant,'scenario':options.scenario,'metric':options.metric,'iteration':options.iteration,'started_utc':now(),'binary_sha256':digest(binary),'source_sha256':source_before,'original_storage_before':original_before,'input_sha256':{},'status':'running'}
 db=None
 try:
  if options.metric=='create_schema_and_client_ns':
   start=time.perf_counter_ns();db=jay.Jay(scenario,folder/'db',binary,env);elapsed=time.perf_counter_ns()-start
   output['timing_boundary']='Exactly Jay(...) construction, as original create_schema_and_client_ns; fresh durable empty instance and three real preparations.'
   assert equal(db.dump(),{t['name']:[] for t in scenario['tables']})
  else:
   copied=folder/'db';copied.mkdir()
   for p in original_folder.glob('*.bend'):shutil.copy2(p,copied/p.name)
   shutil.copytree(original_folder/'storage',copied/'storage')
   db=jay.Jay.__new__(jay.Jay)
   db.s=scenario;db.folder=copied;db.binary=binary;db.env=env;db.handles={};db.setup={}
   db.start(True);db.prepare()
   expected=json.loads((original_folder/'final-data.json').read_text())
   assert equal(db.dump(),expected),'Copied snapshot pre-reopen readback differs'
   start=time.perf_counter_ns();db.reopen();elapsed=time.perf_counter_ns()-start
   output['timing_boundary']='Exactly db.reopen(), including close of an existing three-program prepared service, open startup and three new preparations, as original reopen_and_client_prepare_ns. Clone startup/readback outside timer.'
   assert equal(db.dump(),expected),'Post-reopen full readback differs'
   output['expected_final_data_sha256']=hashlib.sha256(json.dumps(expected,sort_keys=True).encode()).hexdigest()
  output['elapsed_ns']=elapsed;output['setup']=dict(db.setup)
  output['input_sha256']={p.name:digest(p) for p in db.folder.glob('*.bend')}
  output['full_data_check']=True
  db.close();db=None
  assert storage_hashes(root,options.scenario)==original_before,'Original snapshot changed'
  assert digest(binary)==recorded['jay_binary_sha256']
  assert identity()==source_before,'Engine source changed during setup diagnostic'
  output['original_storage_after']=storage_hashes(root,options.scenario)
  output['status']='passed'
 except BaseException as e:
  output['error']=f'{type(e).__name__}: {e}';output['status']='failed';raise
 finally:
  if db is not None:db.close()
  output['finished_utc']=now();save(folder/'result.json',output)


def main():
 p=argparse.ArgumentParser();p.add_argument('--worker',action='store_true');p.add_argument('--root');p.add_argument('--variant');p.add_argument('--scenario');p.add_argument('--metric');p.add_argument('--iteration',type=int);p.add_argument('--folder');o=p.parse_args()
 if o.worker:return worker(o)
 import fcntl
 with open('/tmp/jaydb2-experiments-heavy.lock','w') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  report={'scope':'Separate setup-only follow-up; does not overwrite or pass original full-run gates. Three interleaved paired repetitions per originally flagged metric. Alternate A/B then B/A order. Same canonical durable limits, frozen binaries, actual admission and three prepared programs. No workload timings are replaced.','started_utc':now(),'status':'running','records':[],'cases':CASES,'hardware':{'load_start':os.getloadavg()},'script_sha256':digest(__file__)}
  save(OUT/'result.json',report)
  try:
   for iteration in range(3):
    for scenario,metric in CASES:
     variants=[('baseline',BASELINE),('candidate',CANDIDATE)]
     if iteration%2:variants.reverse()
     for variant,root in variants:
      folder=OUT/f'{scenario}-{metric}-{iteration}-{variant}'
      cmd=[str(root/'build/database-comparison-venv/bin/python'),'-B',__file__,'--worker','--root',str(root),'--variant',variant,'--scenario',scenario,'--metric',metric,'--iteration',str(iteration),'--folder',str(folder)]
      print(now(),scenario,metric,iteration,variant,'start',flush=True)
      with (OUT/'workers.log').open('ab') as log:r=subprocess.run(cmd,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,cwd=root)
      if r.returncode:raise RuntimeError(f'Worker failed {r.returncode}: {folder}; see workers.log')
      record=json.loads((folder/'result.json').read_text());report['records'].append(record);save(OUT/'result.json',report)
      print(now(),scenario,metric,iteration,variant,round(record['elapsed_ns']/1e9,3),'seconds',flush=True)
   summary=[]
   for scenario,metric in CASES:
    pairs=[]
    for i in range(3):
     rows=[r for r in report['records'] if r['scenario']==scenario and r['metric']==metric and r['iteration']==i]
     by={r['engine_variant']:r for r in rows};b,c=by['baseline']['elapsed_ns'],by['candidate']['elapsed_ns']
     pairs.append({'iteration':i,'baseline_ns':b,'candidate_ns':c,'delta_percent':(c/b-1)*100,'candidate_over_baseline':c/b})
    summary.append({'scenario':scenario,'metric':metric,'pairs':pairs,'baseline_median_ns':statistics.median(p['baseline_ns'] for p in pairs),'candidate_median_ns':statistics.median(p['candidate_ns'] for p in pairs),'median_paired_delta_percent':statistics.median(p['delta_percent'] for p in pairs),'min_paired_delta_percent':min(p['delta_percent'] for p in pairs),'max_paired_delta_percent':max(p['delta_percent'] for p in pairs)})
   report['summary']=summary;report['status']='passed'
  except BaseException as e:
   report['status']='failed';report['error']=f'{type(e).__name__}: {e}';raise
  finally:
   report['finished_utc']=now();report['hardware']['load_end']=os.getloadavg();save(OUT/'result.json',report)

if __name__=='__main__':main()
