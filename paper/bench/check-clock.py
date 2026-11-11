#!/usr/bin/env python3
"""Verify real restoration after failure/INT/TERM/HUP; caller holds heavy lock."""
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from paper.bench.frequency import observe


def main():
    recovery=ROOT/'.build/paper-bench'
    originals=list(recovery.glob('frequency-*/original.json'))
    if not originals:raise SystemExit('Run the measurements first: original recovery snapshot required')
    original=min((json.loads(p.read_text()) for p in originals),key=lambda r:r['utc'])
    # Repair any left-over policy before testing the wrapper itself.
    if observe()['settings']!=original['settings']:
        path=min(originals,key=lambda p:json.loads(p.read_text())['utc'])
        subprocess.run(['sudo','-n','python3','-B',str(ROOT/'paper/bench/frequency.py'),'restore',str(path)],check=True)
    tests=[]
    for label,command,status in [('failure','exit 7',7),('INT','kill -INT "$PPID"',130),('TERM','kill -TERM "$PPID"',143),('HUP','kill -HUP "$PPID"',129)]:
        result=subprocess.run([str(ROOT/'paper/bench/fixed-clock.sh'),'bash','-c',command],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        current=observe()
        verified=current['settings']==original['settings']
        tests.append(dict(case=label,command=command,expected_exit=status,actual_exit=result.returncode,restored=verified,output=result.stdout))
        if result.returncode!=status or not verified:
            raise AssertionError(tests[-1])
    runs=[]
    for directory in sorted(recovery.glob('frequency-*')):
        entries={name:json.loads((directory/(name+'.json')).read_text()) for name in ('original','applied','restored')}
        assert entries['applied']['verified'] and entries['restored']['verified']
        assert entries['original']['settings']==entries['restored']['settings']
        runs.append(dict(directory=str(directory.relative_to(ROOT)),**entries))
    final=observe()
    receipt=dict(verified=final['settings']==original['settings'],original=original,final=final,trap_checks=tests,runs=runs)
    assert receipt['verified']
    (ROOT/'paper/evidence/cpu-restoration.json').write_text(json.dumps(receipt,indent=2)+'\n')
    for path,value in final['settings'].items():print(path+' = '+value)
    print('Verified all original CPU settings and failure/INT/TERM/HUP restoration')


if __name__=='__main__':main()
