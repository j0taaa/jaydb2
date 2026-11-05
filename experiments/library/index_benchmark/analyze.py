from pathlib import Path
import os
import hashlib,json,random,statistics
SUITE=Path(__file__).resolve().parent
ROOT=SUITE.parents[2]
OUT=Path(os.environ.get("JAYDB_INDEX_BENCH_OUTPUT",str(ROOT/"build/library/index-benchmark-run"))).resolve()
r=json.loads((OUT/'results.json').read_text())
assert r['status']=='passed',r['status']
checks=[]
lock=r['toolchain_lock']
for name,want in lock['files'].items():
 p=ROOT/'.tools'/('bend-source-'+lock['version'])/name
 actual=hashlib.sha256(p.read_bytes()).hexdigest();assert actual==want,name
 checks.append(dict(path=str(p),sha256=actual))
for p,want in [(ROOT/'.tools'/('bend-'+lock['version'])/'bin/bend',lock['officialBinarySha256']),(ROOT/'.tools'/('bendtt-'+lock['kernelSha256']),lock['kernelSha256'])]:
 actual=hashlib.sha256(p.read_bytes()).hexdigest();assert actual==want,p
 checks.append(dict(path=str(p),sha256=actual))
assert hashlib.sha256((ROOT/'target/release/jaydb2').read_bytes()).hexdigest()==r['binary_sha256']
for name,want in r['sources_sha256'].items():assert hashlib.sha256((OUT/'stage'/name).read_bytes()).hexdigest()==want,name
rng=random.Random(20261105)
def compare(a,b):
 x=a['samples_ns'];y=b['samples_ns'];assert len(x)==len(y)==r['settings']['samples']
 ratios=[v/u for u,v in zip(x,y)]
 boot=sorted(statistics.median(rng.choices(ratios,k=len(ratios))) for _ in range(10000))
 return dict(ratio_of_medians=b['median_ms']/a['median_ms'],median_paired_ratio=statistics.median(ratios),paired_ratio_bootstrap_95=[boot[249],boot[9749]],faster_rounds=sum(v<u for u,v in zip(x,y)),n=len(x))
queries=[]
for c in r['measurements']:
 v=c['results']
 queries.append({k:c[k] for k in ['tag','case','rows','padding_bytes','matches']}|dict(end_to_end=compare(v['base_without_index'],v['indexed_lookup']),same_state=compare(v['base_with_index'],v['indexed_lookup']),index_state_overhead=compare(v['base_without_index'],v['base_with_index'])))
writes=[]
for c in r['writes']:
 writes.append({k:c[k] for k in ['tag','rows','padding_bytes']}|dict(unique=compare(c['results']['none'],c['results']['unique']),many=compare(c['results']['none'],c['results']['many'])))
output=dict(status='passed',checked_requests=r['checked_requests'],verified_toolchain=checks,controller_sha256=r['binary_sha256'],queries=queries,writes=writes,statistics='Ordered sample pairs per comparison; ratio < 1 means index faster. Bootstrap is deterministic resampling of the paired ratios, 10000 draws, percentile 95% interval. It describes this run, not general performance across environments.')
(OUT/'analysis.json').write_text(json.dumps(output,indent=2)+'\n')
lines=['Index benchmark: actual admitted prepared requests','',f"Revision: {r['head']}",f"Controller SHA-256: {r['binary_sha256']}",f"Checked requests: {r['checked_requests']}",'','All tests used the unchanged experiment-library host, official CPU backend, one native thread, no persistence, and an explicit zero-law benchmark configuration. Normal admission, technical validation, current authentication and sealed prepared artifacts remained enabled.',f"{r['settings']['warmups']} warmups and {r['settings']['samples']} measured rounds; rotated/alternating order. Baseline: identical business data with empty index tables. Same-state control: direct scan with index populated. Each unique query stops at its first match; nonunique baseline reads group once per business row. Matching nonunique queries return 1/8 of rows. Both indexes use the real library helpers. Update benchmarks change indexed values and maintain the real ordinary-table indexes. Old key information is supplied to both variants, favoring the index by excluding any extra old-value fetch.",'Every loaded base row and index target/value was checked. Every update was followed by base/index checks, removal checks and nonunique complete-result checks. Expected results computed independently in Python. No universal performance claim.','', 'Command (from experiment-library):','experiments/library/index_benchmark/run.sh','', 'QUERY MEDIANS (milliseconds; ratio indexed / unindexed scan):']
for c,q in zip(r['measurements'],queries):
 v=c['results'];ci=q['end_to_end']['paired_ratio_bootstrap_95']
 lines.append(f"{c['tag']} {c['case']}: plain={v['base_without_index']['median_ms']:.3f}, scan-with-index={v['base_with_index']['median_ms']:.3f}, index={v['indexed_lookup']['median_ms']:.3f}; ratio={q['end_to_end']['ratio_of_medians']:.3f}, paired CI={ci[0]:.3f}..{ci[1]:.3f}")
lines+=['','UPDATE MEDIANS (milliseconds):']
for c in r['writes']:
 v=c['results'];lines.append(f"{c['tag']}: plain={v['none']['median_ms']:.3f}, unique-maintained={v['unique']['median_ms']:.3f}, nonunique-maintained={v['many']['median_ms']:.3f}")
lines+=['','STATE SIZES (canonical bytes):']
for s in r['states']:lines.append(f"{s['tag']} {s['kind']}: {s['canonical_bytes']}")
(OUT/'BENCHMARK.txt').write_text('\n'.join(lines)+'\n')
print('\n'.join(lines[-14:]))

if (OUT/'batch-results.json').exists():
 batch=json.loads((OUT/'batch-results.json').read_text());assert batch['status']=='passed'
 for name,label in [('BatchClient.bend','code'),('BatchProof.bend','proof')]:
  assert hashlib.sha256((SUITE/name).read_bytes()).hexdigest()==batch['submitted_sha256'][label]
 for c in batch['measurements']:
  a=c['results']['base_without_index'];b=c['results']['indexed_lookup']
  c['comparison']=compare(a,b)
  c['speedup_vs_no_index']=a['median_ms']/b['median_ms']
 (OUT/'batch-analysis.json').write_text(json.dumps(batch,indent=2)+'\n')
 with (OUT/'BENCHMARK.txt').open('a') as f:
  f.write('\nBATCH UNIQUE MISSES: base keys enumerated once per transaction; all queries are misses so early exit cannot help the baseline. Positive controls also return exact real matching keys.\n')
  for c in batch['measurements']:
   v=c['results'];f.write(f"{c['queries_per_transaction']} checks: plain={v['base_without_index']['median_ms']:.3f}, index={v['indexed_lookup']['median_ms']:.3f} ms; speedup={c['speedup_vs_no_index']:.3f}\n")
  f.write(f"Total checked actual requests: {r['checked_requests']+batch['checked_requests']}\n")
