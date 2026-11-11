#!/usr/bin/env python3
"""Fresh, serial measurements. Run ONLY under the common flock (see README)."""
import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import select
import shutil
import signal
import sqlite3
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT/'.build/paper-bench/python'))
from tools.client import encode, frame, prepared_frame, unframe
from paper.bench.fixtures import package

BUILD = ROOT/'.build/paper-bench'
OUT = ROOT/'paper/evidence'


def command(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True, stderr=subprocess.STDOUT).strip()


def metadata():
    tracked = command('git', 'ls-files').splitlines()
    source = [p for p in tracked if p.startswith(('server/', 'src/', 'contract/', 'proof/', 'tools/', 'native/'))]
    return dict(commit=command('git','rev-parse','HEAD'), base_commit='95027beddd57b8f0a647f6980d16610497c3bbf0',
        branch=command('git','branch','--show-current'), utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
        cpu=next(x.split(':',1)[1].strip() for x in Path('/proc/cpuinfo').read_text().splitlines() if x.startswith('model name')),
        logical_cpus=os.cpu_count(), kernel=platform.platform(), python=sys.version, sqlite=sqlite3.sqlite_version,
        node=command('node','--version'), clang=command('clang-19','--version').splitlines()[0], rust=command('rustc','--version'),
        cargo=command('cargo','--version'), bend='2.0.39', toolchain=json.loads((ROOT/'tools/admission/toolchain.lock.json').read_text()),
        binary_sha256=hashlib.sha256((ROOT/'target/release/jaydb2').read_bytes()).hexdigest(),
        source_sha256=hashlib.sha256(b''.join(p.encode()+b'\0'+(ROOT/p).read_bytes() for p in source)).hexdigest(),
        dirty=command('git','status','--porcelain').splitlines(), threads=1,
        filesystem=command('findmnt','-T',str(BUILD),'-no','FSTYPE,SOURCE,OPTIONS'),
        clock='time.perf_counter_ns; client send/flush through full framed response; encoding and result validation excluded',
        lock='/tmp/jaydb2-experiments-heavy.lock', warmups=1)


def save(name, data):
    OUT.mkdir(exist_ok=True)
    tmp = OUT/(name+'.tmp')
    tmp.write_text(json.dumps(data, indent=2, allow_nan=False)+'\n')
    tmp.replace(OUT/name)


class Session:
    def __init__(self, folder, name, persistent=False, timing=False):
        self.folder=folder
        self.logpath=BUILD/(name+'.stderr')
        self.errors=self.logpath.open('w+b')
        self.timer=BUILD/(name+'.timing')
        self.timer.unlink(missing_ok=True)
        args=[str(ROOT/'jaydb2'),'--threads','1','--configuration',str(folder/'Configuration.bend'),
            '--seed',str(folder/'Seed.bend'),'--timing-log',str(self.timer)]
        if persistent:
            self.storage=BUILD/(name+'.db')
            if self.storage.exists(): shutil.rmtree(self.storage)
            args += ['--storage',str(self.storage),'--storage-mode','create']
        env=dict(os.environ, TMPDIR=str(BUILD/'tmp'))
        if timing: env['JAYDB_BENCH_TIMING']='1'
        else: env.pop('JAYDB_BENCH_TIMING',None)
        self.p=subprocess.Popen(args,cwd=ROOT,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=self.errors,start_new_session=True)
        self.exchange(frame(dict(code='',proof='',credential='invalid',arguments=None)),dict(status='authentication',value=None))

    def read(self,n):
        result=b''
        while len(result)<n:
            if not select.select([self.p.stdout],[],[],600)[0]: raise TimeoutError(str(self.logpath))
            chunk=os.read(self.p.stdout.fileno(),n-len(result))
            if not chunk: raise RuntimeError(self.logpath.read_text()[-8000:])
            result+=chunk
        return result

    def exchange(self,message,expected):
        offset=os.fstat(self.errors.fileno()).st_size
        started=time.perf_counter_ns()
        self.p.stdin.write(message); self.p.stdin.flush()
        head=self.read(8); body=self.read(int.from_bytes(head,'big'))
        elapsed=time.perf_counter_ns()-started
        actual=unframe(head+body)
        if expected is not None and (type(actual)!=type(expected) or json.dumps(actual,sort_keys=True)!=json.dumps(expected,sort_keys=True)):
            raise AssertionError((actual,expected,self.logpath.read_text()[-6000:]))
        phases={}
        for line in os.pread(self.errors.fileno(),os.fstat(self.errors.fileno()).st_size-offset,offset).decode().splitlines():
            if 'JAYDB_BENCH ' in line:
                event=json.loads(line.split('JAYDB_BENCH ',1)[1]); phases[event['phase']]=int(event['ns'])
        return dict(elapsed_ns=elapsed,actual=actual,expected=expected,checked=expected is not None,phases_ns=phases)

    def call(self,code,proof,args,expected,handle=None,user='alice-token'):
        msg=prepared_frame(1,handle,user,args) if handle else frame(dict(code=code,proof=proof,credential=user,arguments=args))
        return self.exchange(msg,expected)

    def prepare(self,code,proof):
        row=self.exchange(prepared_frame(0,code,'alice-token',None,proof),None)
        assert row['actual']['status']=='prepared', (row,self.logpath.read_text()[-8000:])
        assert re.fullmatch('[a-f0-9]{64}',row['actual']['value'])
        row.update(expected=row['actual'],checked=True)
        return row['actual']['value'],row

    def close(self):
        self.p.stdin.close()
        try:
            assert self.p.wait(timeout=30)==0, self.logpath.read_text()[-3000:]
        finally:
            if self.p.poll() is None: os.killpg(self.p.pid,signal.SIGKILL); self.p.wait()
            self.p.stdout.close(); self.errors.close()


@contextmanager
def session(*args,**kwargs):
    s=Session(*args,**kwargs)
    try: yield s
    finally: s.close()


def source(folder):
    return tuple((folder/name).read_text() for name in ('Client.bend','ClientProof.bend','PreparedProof.bend'))


def operation(kind,i):
    if kind=='read': return ['read','k000000'],0
    if kind=='indexed': return ['set',bool(i%2)],bool(i%2)
    return ['issue',f'r{i:04d}','coffee',False],f'v:r{i:04d}'


def latency():
    data=dict(metadata=metadata(),experiment='E1 ordinary',records=[],limitations=[
        'Oracle soundness is included in primary/BendTT whole-Book phases; no per-law callback exists in pinned APIs.',
        'BendTT phase includes official translation, IO and kernel process; subphases are not separated.',
        'Instrumentation is opt-in; measured client intervals include its small diagnostic cost.',
        'Voucher issue uses a fresh equal-length key per call; index set alternates false/true.'])
    for kind in ('read','indexed','voucher'):
        folder=package(BUILD/('ordinary-'+kind),kind)
        code,proof,_=source(folder)
        record=dict(program=kind,n=10,warmup=[],samples=[])
        with session(folder,'ordinary-'+kind,timing=True) as s:
            for i in range(11):
                args,value=operation(kind,i)
                row=s.call(code,proof,args,dict(status='success',value=value))
                row['iteration']=i
                record['warmup' if i==0 else 'samples'].append(row)
                print('ordinary',kind,i,round(row['elapsed_ns']/1e9,3),flush=True)
        data['records'].append(record); save('ordinary.json',data)


def prepared():
    data=dict(metadata=metadata(),experiment='E2 prepared',records=[])
    for persistent in (False,True):
        for kind in ('read','indexed','voucher'):
            name=f'prepared-{kind}-{persistent}'
            folder=package(BUILD/name,kind)
            code,proof,universal=source(folder)
            record=dict(program=kind,persistent=persistent,n=300,registrations=[],samples=[],warmup=[])
            with session(folder,name,persistent=persistent,timing=True) as s:
                # Three one-time registration observations; discarded handles are
                # invalidated so the measured worker always has one live entry.
                for j in range(3):
                    handle,row=s.prepare(code,universal); record['registrations'].append(row)
                    if j<2: s.exchange(prepared_frame(2,handle,'alice-token'),dict(status='invalidated',value=None))
                for i in range(301):
                    args,value=operation(kind,i)
                    row=s.call(code,proof,args,dict(status='success',value=value),handle=handle)
                    row['iteration']=i
                    if kind=='voucher':
                        maintenance=s.call(code,proof,['retire',f'r{i:04d}'],dict(status='success',value='retired'),handle=handle)
                        row['untimed_retirement_checked']=maintenance['checked']
                    record['warmup' if i==0 else 'samples'].append(row)
            data['records'].append(record); save('prepared.json',data)
            print('prepared',kind,persistent,'complete',flush=True)


def verification():
    data=dict(metadata=metadata(),experiment='E4 verification and sizes',commands=[])
    for target in ('verify-contract','verify','test'):
        started=time.perf_counter_ns()
        result=subprocess.run(['make',target],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        elapsed=time.perf_counter_ns()-started
        (BUILD/(target+'.log')).write_text(result.stdout)
        data['commands'].append(dict(command='make '+target,elapsed_ns=elapsed,returncode=result.returncode,output=result.stdout))
        save('verification.json',data)
        print(target,result.returncode,round(elapsed/1e9,2),flush=True)
    data['sizes']={}
    for group,dirs in [('src',['src']),('contract',['contract']),('proof',['proof']),('server',['server']),('tools',['tools/admission','tools/service']),('native',['native'])]:
        files=[p for base in dirs for p in (ROOT/base).rglob('*') if p.is_file() and p.suffix in ('.bend','.rs','.mjs','.json','.c','.h','.py')]
        data['sizes'][group]=dict(files=len(files),nonblank_lines=sum(sum(bool(line.strip()) for line in p.read_text().splitlines()) for p in files))
    data['negative_fixtures']=len(list((ROOT/'tests/proof/rejected').glob('*.bend')))
    data['theorem_types']=len(re.findall(r'^def \w*Theorem\b',(ROOT/'contract/Theorems.bend').read_text(),re.M))
    data['proof_law_declarations']=sum(len(re.findall(r'^law\s+',p.read_text(),re.M)) for p in (ROOT/'proof').glob('*.bend'))
    data['proof_definitions']=sum(len(re.findall(r'^def\s+',p.read_text(),re.M)) for p in (ROOT/'proof').glob('*.bend'))
    save('verification.json',data)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('experiment',choices=['latency','prepared','comparison','scaling','verification'])
    args=parser.parse_args()
    BUILD.mkdir(parents=True,exist_ok=True); (BUILD/'tmp').mkdir(exist_ok=True)
    if args.experiment in ('comparison','scaling'):
        from paper.bench.workloads import comparison,scaling
        globals().update(comparison=comparison,scaling=scaling)
    globals()[args.experiment]()

if __name__=='__main__': main()
