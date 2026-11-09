#!/usr/bin/env python3
"""Short baseline/private scalar prototype setup mitigation diagnostic."""
from datetime import datetime, timezone
import argparse,hashlib,json,os,re,resource,statistics,subprocess,sys,time
from pathlib import Path
PARENT=Path('/home/jota/projects/jaydb2-performance')
BASELINE=Path('/home/jota/projects/jaydb2-performance-baseline')
SCALAR=PARENT/'build/performance-scalar-prototype/root'
OUT=PARENT/'build/performance-scalar-setup'
CASES=['02_household_budget','04_ecommerce']

def now():return datetime.now(timezone.utc).isoformat()
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(path,value):
 temp=path.with_suffix('.tmp');temp.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n');temp.replace(path)
def original(root):return root/'build/performance-baseline/result.json'
def parent_sources():return json.loads((PARENT/'build/performance-candidate/result.json').read_text())['source_sha256']
def identity(root):
 names=json.loads(original(BASELINE).read_text())['source_sha256'] if root==BASELINE else parent_sources()
 return {n:digest(root/n) for n in names}
def worker(o):
 root=Path(o.root);harness=BASELINE if o.variant=='baseline' else PARENT
 sys.path.insert(0,str(harness/'experiments/database-comparison'))
 import jay
 from model import equal,load
 # Prototype is a private source bundle without copied benchmark files. Only
 # adapter cwd changes; canonical suite and real input/proof/programs stay intact.
 jay.ROOT=root
 before=identity(root)
 if o.variant=='baseline':
  original_manifest=json.loads(original(root).read_text());binary=Path(original_manifest['jay_binary'])
 else:binary=root/'target/release/jaydb2'
 assert digest(binary)==o.expected_binary,'Binary changed'
 scenario=load(harness/'experiments/database-comparison/scenarios'/f'{o.scenario}.json')
 folder=Path(o.folder);folder.mkdir(parents=True,exist_ok=False);tmp=folder/'tmp';tmp.mkdir()
 resource.setrlimit(resource.RLIMIT_STACK,(resource.RLIM_INFINITY,resource.getrlimit(resource.RLIMIT_STACK)[1]))
 env=dict(os.environ,BEND_NO_TELEMETRY='1',BENDRTS='',TMPDIR=str(tmp),CARGO_TARGET_DIR=str(root/'build/database-comparison-target' if o.variant=='baseline' else root/'target'))
 r={'variant':o.variant,'variant_kind':'original frozen baseline' if o.variant=='baseline' else 'private scalar build artifact; not committed production','root':str(root),'harness_root':str(harness),'adapter_binding':'Unmodified Jay adapter; process-local jay.ROOT selects cwd, SUITE remains original canonical harness source directory.','scenario':o.scenario,'metric':'create_schema_and_client_ns','iteration':o.iteration,'binary_sha256':digest(binary),'source_sha256':before,'started_utc':now(),'load_start':os.getloadavg(),'python':sys.version,'status':'running'}
 db=None
 try:
  started=time.perf_counter_ns();db=jay.Jay(scenario,folder/'db',binary,env);elapsed=time.perf_counter_ns()-started
  r['elapsed_ns']=elapsed;r['setup']=dict(db.setup)
  r['c_artifacts']=[]
  for c in tmp.glob('jaydb2-*/*/checked.c'):
   manifest=c.parent/'manifest.json';m=json.loads(manifest.read_text());text=c.read_text()
   row={'artifact':c.parent.name,'c_bytes':c.stat().st_size,'c_sha256':digest(c),'dependencies':len(m['dependencies']),'dependency_bytes':sum((c.parent/f['path']).stat().st_size for f in m['dependencies']),'stats':dict(re.findall(r'#define\s+(STAT_LEN|BANGS)\s+([^\n]+)',text))}
   if (c.parent/'Client.bend').exists():row['client_sha256']=digest(c.parent/'Client.bend')
   r['c_artifacts'].append(row)
  assert equal(db.dump(),{t['name']:[] for t in scenario['tables']}),'Initial empty-state check failed'
  r['full_initial_empty_state_check']=True;r['input_sha256']={p.name:digest(p) for p in db.folder.glob('*.bend')}
  db.close();db=None
  assert identity(root)==before,'Sources changed';assert digest(binary)==o.expected_binary,'Binary changed'
  r['status']='passed'
 except BaseException as e:r['status']='failed';r['error']=f'{type(e).__name__}: {e}';raise
 finally:
  if db is not None:db.close()
  r['finished_utc']=now();r['load_end']=os.getloadavg();save(folder/'result.json',r)

def main():
 p=argparse.ArgumentParser();p.add_argument('--worker',action='store_true');p.add_argument('--root');p.add_argument('--variant');p.add_argument('--scenario');p.add_argument('--iteration',type=int);p.add_argument('--folder');p.add_argument('--expected-binary');o=p.parse_args()
 if o.worker:return worker(o)
 import fcntl
 with open('/tmp/jaydb2-experiments-heavy.lock','w') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  baseline_manifest=json.loads(original(BASELINE).read_text());status=json.loads((SCALAR.parent/'status.json').read_text());assert status['status']=='passed'
  source_maps={v:identity(r) for v,r in [('baseline',BASELINE),('scalar',SCALAR)]}
  expected=parent_sources();diff=sorted(n for n in expected if expected[n]!=source_maps['scalar'][n]);assert diff==['proof/FastBytes.bend','src/FastBytes.bend'],diff
  assert source_maps['baseline']==baseline_manifest['source_sha256'],'Baseline source drift'
  binaries={'baseline':baseline_manifest['jay_binary_sha256'],'scalar':digest(SCALAR/'target/release/jaydb2')}
  report={'scope':'Separate SHORT mitigation diagnostic: baseline versus PRIVATE scalar prototype, fresh create/schema/client preparation only; no original full-run gate or workload sample is replaced. Three interleaved pairs for each of two originally flagged create metrics.','started_utc':now(),'script_sha256':digest(__file__),'prototype_parent_source_differences':diff,'prototype_status_sha256':digest(SCALAR.parent/'status.json'),'source_maps':source_maps,'binaries':binaries,'status':'running','records':[],'hardware':{'orchestrator_python':sys.version,'affinity':sorted(os.sched_getaffinity(0)),'load_start':os.getloadavg()}}
  save(OUT/'result.json',report)
  try:
   for i in range(3):
    for scenario in CASES:
     variants=[('baseline',BASELINE),('scalar',SCALAR)]
     if i%2:variants.reverse()
     for variant,root in variants:
      folder=OUT/f'{scenario}-{i}-{variant}';cmd=[str(PARENT/'build/database-comparison-venv/bin/python'),'-B',__file__,'--worker','--root',str(root),'--variant',variant,'--scenario',scenario,'--iteration',str(i),'--folder',str(folder),'--expected-binary',binaries[variant]]
      print(now(),scenario,i,variant,'start',flush=True)
      with (OUT/'workers.log').open('ab') as log:p=subprocess.run(cmd,cwd=root,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT)
      if p.returncode:raise RuntimeError(f'Worker failed{p.returncode}: {folder}')
      record=json.loads((folder/'result.json').read_text());assert record['source_sha256']==source_maps[variant];report['records'].append(record);save(OUT/'result.json',report);print(now(),scenario,i,variant,round(record['elapsed_ns']/1e9,3),'seconds',flush=True)
   summary=[]
   for scenario in CASES:
    pairs=[]
    for i in range(3):
     by={r['variant']:r for r in report['records'] if r['scenario']==scenario and r['iteration']==i};b,c=by['baseline']['elapsed_ns'],by['scalar']['elapsed_ns'];assert by['baseline']['input_sha256']==by['scalar']['input_sha256'],'Inputs differ'
     pairs.append({'iteration':i,'baseline_ns':b,'scalar_ns':c,'delta_percent':(c/b-1)*100})
    summary.append({'scenario':scenario,'metric':'create_schema_and_client_ns','pairs':pairs,'baseline_median_ns':statistics.median(p['baseline_ns'] for p in pairs),'scalar_median_ns':statistics.median(p['scalar_ns'] for p in pairs),'median_paired_delta_percent':statistics.median(p['delta_percent'] for p in pairs),'min_paired_delta_percent':min(p['delta_percent'] for p in pairs),'max_paired_delta_percent':max(p['delta_percent'] for p in pairs)})
   report['summary']=summary;report['status']='passed'
  except BaseException as e:report['status']='failed';report['error']=f'{type(e).__name__}: {e}';raise
  finally:report['finished_utc']=now();report['hardware']['load_end']=os.getloadavg();save(OUT/'result.json',report)
if __name__=='__main__':main()
