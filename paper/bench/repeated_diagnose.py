#!/usr/bin/env python3
"""Research-only prepared-call capture. Caller holds heavy lock + fixed-clock.sh.

Builds real twice-checked fixtures and records uninstrumented service samples.
Copies already admitted literal C/artifacts for separate profiling; never edits C.
"""
import argparse
import hashlib
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from paper.bench.run import ROOT, BUILD, metadata, package, session, source
from paper.bench.fixtures import bulk_population
from tools.client import encode, prepared_frame


def packet(a,b):
    return len(a).to_bytes(8,'big')+a+b


def state(count):
    return encode(dict(tables=[dict(name='cells',rows=[dict(id=f'k{i:06d}',value=0) for i in range(count)])],
                       users=[dict(credential='alice-token',id='alice',kind='user'),
                              dict(credential='bob-token',id='bob',kind='user')]))


def capture(calls):
    out=BUILD/'repeated'; out.mkdir(parents=True,exist_ok=True)
    (BUILD/'tmp').mkdir(parents=True,exist_ok=True)
    folder=package(out/'fixture','read',10)
    code,proof,universal=source(folder)
    data=dict(metadata=metadata(1),mode='unmodified service, no preload; volatile, threads=1',records=[])
    with session(folder,'repeated',timing=True) as s:
        handle,registration=s.prepare(code,universal)
        live=BUILD/'tmp'/f'jaydb2-{s.p.pid}-0'
        population,certificate=bulk_population(proof)
        ph,_=s.prepare(population,certificate)
        # Start with no population changes and remove its live registration.
        s.exchange(prepared_frame(2,ph,'alice-token'),dict(status='invalidated',value=None))
        for count in (10,1105):
            if count>10:
                ph,_=s.prepare(population,certificate)
                s.call(population,certificate,[f'k{i:06d}' for i in range(count)],
                       dict(status='success',value=count),handle=ph)
                s.exchange(prepared_frame(2,ph,'alice-token'),dict(status='invalidated',value=None))
            for op in ('read','update'):
                rows=[]
                for i in range(calls+1):
                    args=[op,f'k{count-1:06d}']+([i%2] if op=='update' else [])
                    rows.append(s.call(code,proof,args,dict(status='success',value=True if op=='update' else 0),handle=handle))
                data['records'].append(dict(rows=count,operation=op,warmup=rows[:1],samples=rows[1:]))
            # Save exact service artifact directory before Temporary drops it.
            dest=out/f'artifacts-{count}'
            if dest.exists(): shutil.rmtree(dest)
            shutil.copytree(live,dest)
            env=json.loads((live/'environment.json').read_text())['identity']
            # History comes from actual successful preparation receipts, in newest-first order.
            history=[ph,handle] if count==10 else [ph,data['first_population_handle'],handle]
            registry=encode([[[env,handle,code,universal,False,'']],history])
            root=state(count)
            for op in ('read','update'):
                args=[op,f'k{count-1:06d}']+([1] if op=='update' else [])
                body=prepared_frame(1,handle,'alice-token',args)[8:]
                (out/f'{op}-{count}.auth.in').write_bytes(packet(root,body))
                (out/f'{op}-{count}.worker.in').write_bytes(packet(registry,packet(root,body)))
            if count==10: data['first_population_handle']=ph
            data.setdefault('fixtures',[]).append(dict(rows=count,state_bytes=len(root),registry_bytes=len(registry),handle=handle,
                artifact_directory=str(dest.relative_to(ROOT)),live_directory=str(live)))
            (out/'capture.json').write_text(json.dumps(data,indent=2)+'\n')
            print('captured',count,flush=True)
    return data


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--calls',type=int,default=100)
    a=p.parse_args()
    if a.calls<1:p.error('--calls must be positive')
    capture(a.calls)
