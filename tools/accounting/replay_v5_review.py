"""Literal V5 progress regressions, causal freezes and an unresolved lease witness.

Cleanup timeouts bound the harness only; they never represent service K or
FalhaReal. The adapted-lease witness is deliberately not reported as fixed.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import subprocess
import tarfile
import tempfile

ROOT=Path(__file__).resolve().parents[2]

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def load(p,name):
    s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def main():
    work=Path(tempfile.mkdtemp(prefix='jaydb2-retention-v6-causal-'));tracers={};baselines={}
    for version in ('v3','v4','v5'):
        path=ROOT/f'tests/accounting/checkpoints/retention_{version}.json';j=json.loads(path.read_text())
        archive=ROOT/j['archive'];assert sha(archive)==j['archiveSha256']
        with tarfile.open(archive) as t:t.extractall(work/version,filter='data')
        assert all(sha(work/version/p)==v for p,v in j['files'].items())
        tracers[version]=load(work/version/'tools/accounting/build.py',version+'_build').build(work/(version+'-build'))[1]
        baselines[version]={'archive_sha256':sha(archive),'manifest_sha256':sha(path)}
    tracers['current']=load(ROOT/'tools/accounting/build.py','current_build').build(work/'current-build')[1]
    fixtures={'lease':ROOT/'tests/accounting/review_v5/lease_truncate.c',
              'fifo':ROOT/'tests/accounting/review_v5/fifo_variant.c',
              'progress':ROOT/'tests/accounting/progress_probe.c'}
    for name,p in fixtures.items():
        subprocess.run(['/usr/bin/clang-19','-std=c11','-O2','-g','-Wall','-Wextra','-Werror','-pthread',
            '-I',str(ROOT/'native/accounting'),str(p),str(ROOT/'native/accounting/counter.c'),'-o',str(work/name)],check=True)
    runner=load(ROOT/'tests/accounting/review_v4/run_probes.py','literal_runner');runner.P=work
    rows=[];pending=[]
    def run(version,kind,args,mode,attempt,timeout_expected=False,obligation=False):
        runner.EXE=work/kind
        r=runner.run(f'{version}-{kind}-{mode}-{attempt}',args,observed=mode!='control',report=mode=='report',
                     timeout=2,tracer=tracers[version])
        assert r['timed_out']==timeout_expected,r
        if not timeout_expected:
            assert r['returncode']==0 and 'FACT completed 1' in r['stdout'],r
            if kind=='lease':assert 'FACT lease_handler_result 0 errno 0' in r['stdout'],r
        r.update(version=version,case=kind,attempt=attempt,mode=mode,
                 status='unresolved-adapted-lease' if obligation else 'causal-expectation-confirmed')
        (pending if obligation else rows).append(r)
        print(version,kind,mode,attempt,r['status'],'cleanup_timeout' if timeout_expected else 'completed',flush=True)
    for version in ('v5','current'):
        for attempt in range(3):
            for kind,args in [('lease',['@DIR@']),('fifo',['fifo','@DIR@',1,1])]:
                for mode in ('control','report','no-report'):
                    run(version,kind,args,mode,attempt,version=='v5' and mode!='control')
        for operation in range(4):
            for mode in ('report','no-report'):
                run(version,'progress',[f'regular_lease{operation}','@DIR@'],mode,operation,version=='v5')
    for version in ('v3','v4'):
        for kind,args in [('lease',['@DIR@']),('fifo',['fifo','@DIR@',1,1])]:
            for mode in ('report','no-report'):
                run(version,kind,args,mode,0,version=='v4' and kind=='fifo')
    for mode in ('control','report','no-report'):
        run('current','progress',['adapted_lease'],mode,'adapted-obligation',mode!='control',obligation=True)
    for version,b in baselines.items():
        path=ROOT/f'tests/accounting/checkpoints/retention_{version}.json';j=json.loads(path.read_text())
        assert sha(path)==b['manifest_sha256'] and sha(ROOT/j['archive'])==b['archive_sha256']
    output=ROOT/'tests/accounting/REVIEW_V5_RESULTS.json'
    output.write_text(json.dumps({'successful':True,'complete_service_measurement':False,'evidence_directory':str(work),
        'results':rows,'unresolved_obligations':pending,'baselines':baselines,
        'current_build':json.loads((work/'current-build/BUILD.json').read_text()),
        'fixture_sha256':{str(p.relative_to(ROOT)):sha(p) for p in fixtures.values()},
        'timeout_meaning':'bounded harness cleanup, never FalhaReal, resource excess or service K',
        'adapted_lease_progress_solved':False},indent=2)+'\n')
    print(output,flush=True)

if __name__=='__main__':main()
