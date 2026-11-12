#!/usr/bin/env python3
"""Refresh all paper evidence with clean metadata; caller holds the heavy lock.
Each fixed-clock invocation restores CPU policy before the next experiment.
Intermediate outputs stay ignored until every harness and restoration check pass.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from paper.bench.frequency import observe


def main():
    os.chdir(ROOT)
    out=ROOT/'.build/paper-bench'/time.strftime('refresh-%Y%m%dT%H%M%SZ',time.gmtime())
    out.mkdir(parents=True)
    revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
    results=[]
    def run(label,command,evidence=None,staged=None):
        assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip(), 'dirty before '+label
        started=time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT)
        record=dict(label=label,command=command,revision=revision,seconds=time.monotonic()-started,returncode=result.returncode)
        if evidence:
            path=ROOT/'paper/evidence'/evidence
            if path.exists():
                shutil.copy2(path,out/(staged or evidence))
                path.write_bytes(subprocess.check_output(['git','show','HEAD:paper/evidence/'+evidence]))
        current=observe()
        valid=len(current['settings'])==33 and all(v==('0' if p.endswith('/no_turbo') else 'powersave' if p.endswith('/scaling_governor') else 'balance_performance') for p,v in current['settings'].items())
        record.update(cpu_restored=valid,cpu_readback=current)
        if evidence and (out/(staged or evidence)).exists():
            record['evidence_sha256']=hashlib.sha256((out/(staged or evidence)).read_bytes()).hexdigest()
        results.append(record)
        (out/'refresh-log.json').write_text(json.dumps(results,indent=2)+'\n')
        print(json.dumps({k:v for k,v in record.items() if k!='cpu_readback'}),flush=True)
        if result.returncode or not valid:raise SystemExit('STOP: failed '+label+'; inspect '+str(out))
        if label=='verification' and any(c['returncode'] for c in json.loads((out/evidence).read_text())['commands']):
            raise SystemExit('STOP: E4 gate failed; inspect '+str(out))
    run('build',['make','build'])
    for name,filename in [('latency','ordinary.json'),('prepared','prepared.json'),('comparison','comparison.json'),('scaling','scaling.json'),('verification','verification.json')]:
        run(name,['paper/bench/fixed-clock.sh','python3','-B','paper/bench/run.py',name],filename)
    run('source-sizes',['paper/bench/fixed-clock.sh','python3','-B','-m','paper.bench.source_sizes','--update'],'verification.json','inventory.json')
    verification=json.loads((out/'verification.json').read_text());inventory=json.loads((out/'inventory.json').read_text())
    for key in ('detailed_sizes','size_collection_metadata','size_collection_note'):verification[key]=inventory[key]
    (out/'verification.json').write_text(json.dumps(verification,indent=2)+'\n')
    next(r for r in results if r['label']=='verification').update(inventory_enriched=True,evidence_sha256=hashlib.sha256((out/'verification.json').read_bytes()).hexdigest())
    for label,script,filename in [('gpu-programs','gpu_programs.py','gpu-programs.json'),('simulation','simulation.py','simulation.json')]:
        run(label,['paper/bench/fixed-clock.sh','python3','-B','paper/bench/'+script,'--output','paper/evidence/'+filename],filename)
    run('clock-restoration',['python3','-B','paper/bench/check-clock.py'],'cpu-restoration.json')
    # Publication changes tracked files only after all measurements have finished.
    for name in ('ordinary','prepared','comparison','scaling','verification','gpu-programs','simulation','cpu-restoration'):
        shutil.copy2(out/(name+'.json'),ROOT/'paper/evidence'/(name+'.json'))
    shutil.copy2(out/'refresh-log.json',ROOT/'paper/evidence/refresh-log.json')
    print('Complete refresh retained in '+str(out),flush=True)


if __name__=='__main__':main()
