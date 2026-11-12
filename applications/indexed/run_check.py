#!/usr/bin/env python3
"""Focused official-proof and real restricted indexed-business-flow gate.

Invoke under flock /tmp/jaydb2-experiments-heavy.lock. All artifacts are local.
"""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

import check
import negative_cases

ROOT = check.ROOT
sys.path.insert(0,str(ROOT))
from tools.bend import environment, executable
from tools.client import frame, unframe

BUILD = ROOT/'build/library'


def positive(root):
    subprocess.run([sys.executable,'-B',str(ROOT/'tools/check.py'),'--timeout','120',str(root)],check=True,cwd=ROOT)


def rejected(kind,root):
    for mode in ('--check-only','--verdict'):
        p=subprocess.run([str(executable()),str(root),mode],env=environment(),capture_output=True,text=True,timeout=120)
        output=p.stdout+p.stderr
        (BUILD/f'indexed-{kind}-{mode[2:]}.log').write_text(output)
        assert p.returncode and 'SOME PROOFS FAIL' in output and '- expected :' in output and '- observed :' in output,output
        assert 'a defined name' not in output and 'a filled definition' not in output,output
        if kind in ('omitted','forged'):
            # The adapted ordinary operation/layout proofs reach the terminal
            # EXACT index-row equality, with actual old/forged versus required rows.
            assert 'Location: set_alice' in output and 'D.Field{"target"' in output and 'D.Field{"value"' in output,output
            assert 'M.Laid' in output and 'L.Both{{==},{==}}' in output,output
            if kind=='omitted': assert 'Key.part(M.tag(a)' in output,output
            else: assert 'D.VText{"forged"}' in output and 'D.VText{"item"}' in output,output
        else:
            assert 'Location: query_alice' in output and '- expected : False{}' in output and '- observed : True{}' in output,output
        print(f'PASS intended {kind} rejection {mode}',flush=True)


class Database:
    def __init__(self,p,directory):
        self.p=p
        self.code=(directory/'Client.bend').read_text()
        self.proof=(directory/'ClientProof.bend').read_text()

    def call(self,who,args,code=None,proof=None):
        self.p.stdin.write(frame(dict(credential=who+'-token',arguments=args,
            code=self.code if code is None else code,proof=self.proof if proof is None else proof)))
        self.p.stdin.flush()
        header=self.p.stdout.read(8)
        assert len(header)==8,'host exited; inspect build/library/indexed-host.log'
        body=self.p.stdout.read(int.from_bytes(header,'big'))
        return unframe(header+body)


def session(variants):
    with tempfile.TemporaryDirectory(prefix='indexed-session-',dir=BUILD) as tmp, (BUILD/'indexed-host.log').open('w+b') as errors:
        d=Path(tmp)
        check.prepare(d)
        env=dict(os.environ,TMPDIR=str(BUILD/'tmp'),BENDRTS='--gpu-build --help')
        with subprocess.Popen([str(ROOT/'jaydb2'),'--threads','1','--configuration',str(d/'Configuration.bend'),'--seed',str(d/'Seed.bend')],
                cwd=ROOT,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=errors) as p:
            db=Database(p,d)
            def call(who,args,value):
                result=db.call(who,args)
                assert result==dict(status='success',value=value),(who,args,result,value)
            call('alice',['query',False],['item'])
            call('alice',['query',True],[])
            call('bob',['query',False],['item'])
            call('alice',['set',True],True)
            call('alice',['query',True],['item'])
            call('alice',['query',False],[])
            call('bob',['query',False],['item'])
            call('alice',['rebuild'],'rebuilt')
            call('alice',['query',True],['item'])
            for kind,args in [('omitted',['set',False]),('forged',['set',False]),('forbidden',['query',True])]:
                code,proof=variants[kind]
                result=db.call('alice',args,code,proof)
                assert result==dict(status='certificate',value=None),(kind,result)
                call('alice',['query',True],['item'])
                call('alice',['query',False],[])
                call('bob',['query',False],['item'])
            call('alice',['set',False],False)
            call('alice',['query',False],['item'])
            call('alice',['rebuild'],'rebuilt')
            call('bob',['set',True],True)
            call('bob',['query',True],['item'])
            call('bob',['query',False],[])
            call('bob',['rebuild'],'rebuilt')
            call('bob',['query',True],['item'])
            call('alice',['query',False],['item'])
            p.stdin.close()
            p.stdout.close()
        assert p.returncode==0,p.returncode
        errors.seek(0)
        diagnostics=errors.read().decode('utf-8','replace')
        assert len(re.findall(r'^jaydb2: PRIMARY_CHECK: Error:$',diagnostics,re.M))==3,diagnostics
        assert diagnostics.count('Location: set_alice')==2 and diagnostics.count('Location: query_alice')==1,diagnostics
    print('PASS real indexed session: restricted Alice/Bob availability updates, X.scan_equal matching/nonmatching queries, X.maintain and X.rebuild, three intended certificate rejections, unchanged state after each denial, inherited BENDRTS neutralized.',flush=True)


def main():
    BUILD.mkdir(parents=True,exist_ok=True)
    (BUILD/'tmp').mkdir(exist_ok=True)
    positive(check.proof_root())
    variants={}
    for kind in ('omitted','forged','forbidden'):
        code,proof=negative_cases.variant(kind)
        variants[kind]=(code,proof)
        if kind!='forbidden':
            permissions=check.proof_root(BUILD/f'indexed-{kind}-permissions',code,proof,negative_cases.permission_proof(kind))
            positive(permissions)
            print(f'PASS {kind}: independently proved ordinary permissions on ALL valid states and ALL prefixes',flush=True)
        root=check.proof_root(BUILD/f'indexed-{kind}',code,proof)
        rejected(kind,root)
    session(variants)


if __name__=='__main__':
    main()
