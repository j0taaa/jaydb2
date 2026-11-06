#!/usr/bin/env python3
"""Check SQL-generated universal certificates with both official checking modes.

Development only. Caller holds /tmp/jaydb2-experiments-heavy.lock.
"""
from pathlib import Path
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / 'examples' / 'starter'))
from tools.bend import environment, executable
from check import stage
from prepare import prepare


def main() -> None:
    key = {'kind': 'parameter', 'index': 0}
    columns = [{'column': name, 'alias': name}
               for name in ('id', 'title', 'completed', 'owner')]
    cases = {
        'select': {'kind': 'select', 'table': 'tasks', 'columns': columns, 'key': key},
        'insert': {'kind': 'insert', 'table': 'tasks', 'columns': ['id', 'title', 'completed'],
                   'rows': [[key, key, key]], 'returning': columns},
        'insert-two': {'kind': 'insert', 'table': 'tasks', 'columns': ['id', 'title', 'completed'],
                       'rows': [[key, key, key]] * 2, 'returning': columns},
        'update': {'kind': 'update', 'table': 'tasks', 'assignments': [{'column': 'title', 'value': key}],
                   'key': key, 'returning': columns},
        'delete': {'kind': 'delete', 'table': 'tasks', 'key': key, 'returning': columns},
    }
    script = '''import { compileBend } from './clients/sql/src/bend.ts';
let input = ''; for await (const chunk of process.stdin) input += chunk;
process.stdout.write(JSON.stringify(compileBend(JSON.parse(input))));'''
    bend = executable()
    with tempfile.TemporaryDirectory(prefix='jaydb-sql-proofs-') as tmp:
        for label, statement in cases.items():
            project = Path(tmp) / label
            project.mkdir()
            prepare(project)
            compiled = subprocess.run(['node', '--input-type=module', '-e', script],
                                      cwd=ROOT, input=json.dumps(statement), text=True,
                                      capture_output=True, check=True)
            program = json.loads(compiled.stdout)
            (project / 'Client.bend').write_text(program['code'])
            (project / 'PreparedProof.bend').write_text(program['proof'])
            target = Path(tmp) / (label + '-pure')
            target.mkdir()
            stage(project, target)
            for mode in ('--check-only', '--verdict'):
                result = subprocess.run([str(bend), str(target / 'Check.bend'), mode],
                                        cwd=ROOT, env=environment(), text=True,
                                        capture_output=True, timeout=180)
                output = result.stdout + result.stderr
                if result.returncode or 'ALL PROOFS CHECK' not in output:
                    raise AssertionError(f'{label} {mode}\n{output}')
                print(f'PASS SQL {label} {mode}', flush=True)


if __name__ == '__main__':
    main()
