from pathlib import Path
import json,hashlib,subprocess,sys
sys.path.insert(0,'experiments/database-comparison')
from compare import load_manifest
paths=[Path('/home/jota/projects/jaydb2-performance-baseline/build/performance-baseline/result.json'),Path('/home/jota/projects/jaydb2-performance/build/performance-candidate/result.json'),Path('/home/jota/projects/jaydb2-performance/build/performance-query/result.json'),Path('build/performance-final-engine/result.json').resolve(),Path('build/performance-final-query/result.json').resolve()]
checks=[];hashes={};n=0
for path in paths:
 m=load_manifest(path)[0];assert m['status']=='passed' and len(m['results'])==30
 repo=Path(m['output']).parents[1]
 for name,digest in m['source_sha256'].items():
  raw=subprocess.check_output(['git','-C',str(repo),'show',m['git_head']+':'+name])
  assert hashlib.sha256(raw).hexdigest()==digest,(path,name)
 for name,digest in m['suite_sha256'].items():
  assert hashlib.sha256((Path(m['output'])/'suite'/name).read_bytes()).hexdigest()==digest,(path,name)
 assert hashlib.sha256(Path(m['jay_binary']).read_bytes()).hexdigest()==m['jay_binary_sha256']
 for r in m['results']:
  data=json.loads((Path(m['output'])/r['scenario']/r['engine']/'final-data.json').read_text())
  digest=hashlib.sha256(json.dumps(data,sort_keys=True).encode()).hexdigest()
  assert digest==r['final_data_sha256']
  hashes.setdefault(r['scenario'],set()).add(digest)
  n+=sum(s['phase']=='sample' for s in r['samples'])
 checks.append({'result_path':str(path),'manifest_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'databases':30,'source_files_checked':len(m['source_sha256']),'controller_sha256':m['jay_binary_sha256']})
assert n==5145 and all(len(x)==1 for x in hashes.values())
report={'status':'passed','database_runs':150,'measured_samples':n,'final_hashes_match_all15_records_per_scenario':True,'runs':checks,'scope':'Recomputed summaries/checked exact-type samples via comparator loader; matched recorded engine source to recorded commits, current retained binaries to hashes, and each final-data file to recorded digest. No native/database process is started.'}
out=Path('experiments/database-comparison/evidence/performance/all-runs-audit.json');out.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(json.dumps(report,indent=2))
