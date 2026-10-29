"""Paired literal V7 SIGKILL reproduction; no independent review is launched.

The same fixture executable (built with frozen V7 counter.c) runs under the
frozen and current observers, so wrapper cleanup does not confound this local
availability comparison. The normal suite separately builds all live inputs.
An intermittent old failure is recorded, never synthesized or required in a
particular fixed sample. The pre-build reproduction is preserved separately.
"""
from pathlib import Path
import collections
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
    work=Path(tempfile.mkdtemp(prefix='jaydb2-retention-v8-causal-'))
    path=ROOT/'tests/accounting/checkpoints/retention_v7.json';j=json.loads(path.read_text())
    archive=ROOT/j['archive'];assert sha(archive)==j['archiveSha256']
    with tarfile.open(archive) as t:t.extractall(work/'v7',filter='data')
    assert all(sha(work/'v7'/p)==v for p,v in j['files'].items())
    load(work/'v7/tools/accounting/build.py','old_build').build(work/'v7-build')
    load(ROOT/'tools/accounting/build.py','new_build').build(work/'current-build')
    fixture=ROOT/'tests/accounting/review_v7/lifecycle.c'
    subprocess.run(['/usr/bin/clang-19','-std=c11','-O2','-g','-fno-builtin','-Wall','-Wextra','-Werror','-pthread',
        '-I',str(work/'v7/native/accounting'),str(fixture),str(work/'v7/native/accounting/counter.c'),'-o',str(work/'lifecycle')],check=True)
    runner=load(ROOT/'tests/accounting/review_v7/harness.py','literal_runner');runner.A=work;rows=[]
    for attempt in range(24):
        for report in (True,False):
            for version in ('v7','current'):
                x=runner.run(f'{version}-kill-{report}-{attempt}',work/'lifecycle',['kill'],version=version,report=report,timeout=4)
                assert not x['timeout_cleanup'],x
                if version=='current':assert x['returncode']==0,x
                else:
                    assert x['returncode'] in (0,125),x
                    if x['returncode']==125:assert x['stderr']=='jayacct: unsupported syscall architecture\n',x
                if x['returncode']==0 and report:
                    s=x['samples'];base=int(s['baseline']['traced_shared_bytes'])
                    assert all(int(s[k]['traced_shared_bytes'])-base==n for k,n in {
                        'owner_before_fork':1048576,'fork_cow_distinct':1048576,'only_child_view':1048576,'closed':0}.items()),x
                    assert not x['summary']['complete'] and x['summary']['unsupported_object_events']==0,x
                x.update(version=version,attempt=attempt,report_enabled=report);rows.append(x)
    for attempt in range(3):
        for mode,version in [('kill',None),('exec',None),('exec','v7'),('exec','current')]:
            x=runner.run(f'control-{mode}-{version}-{attempt}',work/'lifecycle',[mode],version=version,timeout=4)
            assert x['returncode']==0 and not x['timeout_cleanup'],x
            x.update(version=version,attempt=attempt);rows.append(x)
    counts={v:{str(report):dict(collections.Counter(x['returncode'] for x in rows
        if x['version']==v and x.get('report_enabled') is report)) for report in (True,False)} for v in ('v7','current')}
    output=ROOT/'tests/accounting/REVIEW_V7_RESULTS.json';assert not output.exists()
    output.write_text(json.dumps({'successful':True,'complete_service_measurement':False,'evidence_directory':str(work),
        'results':rows,'kill_counts':counts,'baseline':{'manifestSha256':sha(path),'archiveSha256':sha(archive)},
        'fixture_sha256':sha(fixture),'fixture_counter_sources':json.loads((work/'v7-build/BUILD.json').read_text())['sources'],
        'current_build':json.loads((work/'current-build/BUILD.json').read_text()),
        'scope':'local lifecycle availability, not DB reachability or general Linux certification',
        'closureFinal':False},indent=2)+'\n');print(json.dumps(counts),flush=True)
if __name__=='__main__':main()
