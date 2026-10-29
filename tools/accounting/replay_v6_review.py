"""Reproduce the two literal V6 numerical findings and their causal controls.

Build frozen V5/V6 and current sources in a fresh directory. The literal
fixtures and runner remain unchanged. No reachability or completeness verdict
is inferred from these local runs.
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
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
    work=Path(tempfile.mkdtemp(prefix='jaydb2-retention-v7-causal-'));baselines={}
    for v in ('v5','v6'):
        path=ROOT/f'tests/accounting/checkpoints/retention_{v}.json';j=json.loads(path.read_text())
        archive=ROOT/j['archive'];assert sha(archive)==j['archiveSha256']
        with tarfile.open(archive) as t:t.extractall(work/v,filter='data')
        assert all(sha(work/v/p)==h for p,h in j['files'].items())
        load(work/v/'tools/accounting/build.py',v+'_builder').build(work/(v+'-build'))
        baselines[v]={'manifestSha256':sha(path),'archiveSha256':sha(archive)}
    load(ROOT/'tools/accounting/build.py','current_builder').build(work/'current-build')
    fixtures={n:ROOT/f'tests/accounting/review_v6/{n}.c' for n in ('private_owner','anon_ignored_fd')}
    for name,p in fixtures.items():
        subprocess.run(['/usr/bin/clang-19','-std=c11','-O2','-g','-Wall','-Wextra','-Werror','-pthread',
            '-I',str(ROOT/'native/accounting'),str(p),str(ROOT/'native/accounting/counter.c'),'-o',str(work/name)],check=True)
    runner=load(ROOT/'tests/accounting/review_v6/harness.py','literal_runner');runner.A=work
    rows=[]
    for attempt in range(3):
        for version in (None,'v5','v6','current'):
            for fixture,modes in [('private_owner',('private','shared','keepfd','aliases','fork')),
                                  ('anon_ignored_fd',('memfd','minus1'))]:
                for mode in modes:
                    r=runner.run(f'{version}-{fixture}-{mode}-{attempt}',work/fixture,[mode],version=version)
                    assert r['returncode']==0 and not r['timeout_cleanup'],r
                    r.update(version=version,fixture=fixture,mode=mode,attempt=attempt)
                    if version:
                        s=r['samples'];base=int(s['baseline']['traced_shared_bytes'])
                        stage=('child_only_view' if mode=='fork' else 'fd_kept' if mode=='keepfd' else 'only_view') if fixture=='private_owner' else 'acquired'
                        expected=0 if version in ('v5','v6') and mode in ('private','aliases','fork','memfd') else 1048576
                        actual=int(s[stage]['traced_shared_bytes'])-base;assert actual==expected,r
                        assert int(s['closed']['traced_shared_bytes'])==base,r
                        if version=='current' and fixture=='private_owner':
                            assert int(s['child_revoked_view' if mode=='fork' else 'revoked_view']['traced_shared_bytes'])-base==1048576,r
                        assert not r['summary']['complete'] and r['summary']['unsupported_object_events']==0
                        r.update(compared_stage=stage,observed_shared_delta=actual,causal_expected_shared_delta=expected,
                                 known_numeric_mismatch=version!='current' and expected==0)
                    rows.append(r)
    for v,b in baselines.items():
        path=ROOT/f'tests/accounting/checkpoints/retention_{v}.json';j=json.loads(path.read_text())
        assert sha(path)==b['manifestSha256'] and sha(ROOT/j['archive'])==b['archiveSha256']
    output=ROOT/'tests/accounting/REVIEW_V6_RESULTS.json'
    output.write_text(json.dumps({'successful':True,'complete_service_measurement':False,'evidence_directory':str(work),
        'results':rows,'baselines':baselines,'current_build':json.loads((work/'current-build/BUILD.json').read_text()),
        'fixture_sha256':{str(p.relative_to(ROOT)):sha(p) for p in fixtures.values()},
        'scope':'two local numerical findings; neither DB reachability nor absence established',
        'adaptedLeaseProgressSolved':False,'closureFinal':False},indent=2)+'\n')
    print(output,flush=True)

if __name__=='__main__':main()
