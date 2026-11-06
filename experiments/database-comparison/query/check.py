#!/usr/bin/env python3
"""Real native tests for generic transaction-local SUM/JOIN; caller holds heavy lock."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent))
from jay import Jay, configuration, literal, seed


def scenario():
    return {'id': 'generic_query_checks', 'tables': [
        {'name': 'numbers', 'columns': [{'name': 'id', 'type': 'text'},
                                       {'name': 'value', 'type': 'integer'}], 'rows': []},
        {'name': 'parents', 'columns': [{'name': 'id', 'type': 'text'},
                                       {'name': 'name', 'type': 'text'}], 'rows': []},
        {'name': 'children', 'columns': [{'name': 'id', 'type': 'text'},
                                        {'name': 'parent_id', 'type': 'text'}], 'rows': []},
    ]}


def check_proofs(output, record):
    """Stage pure books only; run both official checkers without C/native builds."""
    from tools.bend import environment, executable
    from optimized import read_row_proof
    compiler = executable()
    programs = [(name, (HERE/f'{name}.bend').read_text(),
                 (HERE/f'{name}Proof.bend').read_bytes(), False) for name in ('Sum', 'Join')]
    programs += [('Reader', (HERE/'Read.bend').read_text(), (HERE/'ReadProof.bend').read_bytes(), True),
                 ('ReadRow', (HERE.parent/'ReadRow.bend').read_text(), read_row_proof().encode(), True)]
    for name, code, proof, read_only in programs:
        folder = output/name
        folder.mkdir()
        for directory in ('contract', 'src'):
            for source in (ROOT/directory).glob('*.bend'):
                (folder/source.name).write_text(source.read_text().replace('../contract/', './'))
        (folder/'Client.bend').write_text(code)
        (folder/'ClientProof.bend').write_bytes(proof)
        (folder/'Configuration.bend').write_text(configuration(scenario()))
        (folder/'Seed.bend').write_text(seed(scenario()))
        (folder/'Environment.bend').write_text('import Base\ndef identity() -> String:\n  "generic-query-proof-check"\n')
        (folder/'Instance.bend').write_text('import ./Configuration.bend as C\nimport ./Semantics.bend as S\ndef config() -> S.Configuration: C.config()\n')
        (folder/'Bindings.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Interface.bend as F
import ./ReadOnly.bend as RO
import ./Instance.bend as I
import ./Client.bend as Client
def code() -> String:
  '''+literal(code)+'''
law certificate:
  @ctx: D.Context -> @args: D.Value -> R.Certifies(I.config(), code(), Client.program(), ctx, args)
law terminates:
  F.ProgramTerminates(I.config(), Client.program())
'''+('\nlaw read_only:\n  RO.Program(Client.program())\n' if read_only else ''))
        (folder/'Check.bend').write_text('import ./ClientProof.bend as Proof\nimport ./Seed.bend as Seed\n')
        for option in ('--check-only', '--verdict'):
            result = subprocess.run([str(compiler), str(folder/'Check.bend'), option],
                                    env=environment(), capture_output=True, text=True, timeout=180)
            log = folder/(option.removeprefix('--')+'.txt')
            log.write_text(result.stdout+result.stderr)
            if result.returncode or 'ALL PROOFS CHECK' not in result.stdout:
                raise RuntimeError(f'{name} {option} failed; {log}\n'+result.stdout+result.stderr)
            record['checks'].append({'name': name+' '+option, 'checked': True})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--binary', type=Path, default=ROOT/'target/release/jaydb2')
    parser.add_argument('--check-only', action='store_true', help='Only both official proof checkers; no native build or database')
    args = parser.parse_args()
    output = (ROOT/args.output).resolve()
    if not output.is_relative_to(ROOT/'build'):
        parser.error('output must be a new directory under this checkout build/')
    output.mkdir(parents=True, exist_ok=False)
    (output/'tmp').mkdir()
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.getrlimit(resource.RLIMIT_STACK)[1]))
    env = dict(os.environ, TMPDIR=str(output/'tmp'), BEND_NO_TELEMETRY='1', BENDRTS='')
    record = {'status': 'running', 'checks': [], 'source_sha256': {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.glob('*.bend'))}}
    database = None

    def same(actual, expected):
        if type(actual) is not type(expected):
            return False
        if isinstance(expected, dict):
            return actual.keys() == expected.keys() and all(same(actual[k], expected[k]) for k in expected)
        if isinstance(expected, list):
            return len(actual) == len(expected) and all(same(x, y) for x, y in zip(actual, expected, strict=True))
        return actual == expected

    def check(label, actual, expected):
        if not same(actual, expected):
            raise AssertionError(f'{label}: expected {expected!r}, got {actual!r}')
        record['checks'].append({'name': label, 'actual': actual, 'expected': expected, 'checked': True})

    def call(name, arguments):
        return database.exchange(1, database.handles[name], arguments)

    try:
        if args.check_only:
            check_proofs(output, record)
            record['status'] = 'passed'
            print(f'Both official checkers passed for SUM, JOIN, Reader and ReadRow: {output}/result.json')
            return
        database = Jay(scenario(), output/'database', args.binary.resolve(), env)
        for name in ('Sum', 'Join'):
            code = (HERE/f'{name}.bend').read_text()
            proof = (HERE/f'{name}Proof.bend').read_text()
            result = database.exchange(0, code, proof=proof)
            check(name+' actual universal preparation', result['status'], 'prepared')
            database.handles[name] = result['value']
        check('empty integer table sums to zero', call('Sum', ['sum', 'numbers', 'value']),
              {'status': 'success', 'value': 0})
        check('empty child table joins to empty list', call('Join', ['join', 'children', 'parent_id', 'parents', 'name']),
              {'status': 'success', 'value': []})
        values = [17, -9, 22, 0, -31, 45, -7, 19, -8, 3, 14, -2, 6]
        for i, value in enumerate(values):
            database.put('numbers', {'id': f'k{i:03}', 'value': value})
        check('sum scans all thirteen rows including negative values', call('Sum', ['sum', 'numbers', 'value']),
              {'status': 'success', 'value': sum(values)})
        for i in range(13):
            database.update('numbers', f'k{i:03}', 'value', 0)
        database.update('numbers', 'k000', 'value', -(2**63))
        check('INT64_MIN exact result', call('Sum', ['sum', 'numbers', 'value']),
              {'status': 'success', 'value': -(2**63)})
        database.update('numbers', 'k000', 'value', 2**63-1)
        check('INT64_MAX exact result', call('Sum', ['sum', 'numbers', 'value']),
              {'status': 'success', 'value': 2**63-1})
        database.update('numbers', 'k001', 'value', 1)
        check('positive signed overflow refuses', call('Sum', ['sum', 'numbers', 'value']),
              {'status': 'refusal', 'value': 'integer sum overflow'})
        check('overflow leaves data unchanged', database.get('numbers', 'k000', 'value'), 2**63-1)
        database.update('numbers', 'k000', 'value', -(2**63))
        database.update('numbers', 'k001', 'value', -1)
        check('negative signed overflow refuses', call('Sum', ['sum', 'numbers', 'value']),
              {'status': 'refusal', 'value': 'integer sum overflow'})
        database.update('numbers', 'k000', 'value', -100)
        database.update('numbers', 'k001', 'value', 99)
        check('mixed signs across word carry', call('Sum', ['sum', 'numbers', 'value']),
              {'status': 'success', 'value': -1})
        names = ['Aster', 'Birch', 'Cedar']
        for i, name in enumerate(names):
            database.put('parents', {'id': f'p{i}', 'name': name})
        for i in range(13):
            database.put('children', {'id': f'k{i:03}', 'parent_id': f'p{i%3}'})
        expected = [[f'k{i:03}', names[i%3]] for i in range(13)]
        check('join scans thirteen children with repeated parent keys',
              call('Join', ['join', 'children', 'parent_id', 'parents', 'name']),
              {'status': 'success', 'value': expected})
        database.update('children', 'k005', 'parent_id', 'missing')
        check('inner join skips missing parents without truncating later children',
              call('Join', ['join', 'children', 'parent_id', 'parents', 'name']),
              {'status': 'success', 'value': [p for p in expected if p[0] != 'k005']})
        check('sum refuses noninteger cells', call('Sum', ['sum', 'parents', 'name']),
              {'status': 'refusal', 'value': 'sum requires integer cells'})
        check('join refuses nontext foreign-key cells',
              call('Join', ['join', 'numbers', 'value', 'parents', 'name']),
              {'status': 'refusal', 'value': 'join requires text foreign keys'})
        check('malformed SUM arguments refuse', call('Sum', ['sum', 'numbers']),
              {'status': 'refusal', 'value': 'expected [sum, table, integer_column]'})
        check('malformed JOIN arguments refuse', call('Join', ['join', 'children']),
              {'status': 'refusal', 'value': 'expected [join, child, foreign_key, parent, parent_column]'})
        record['status'] = 'passed'
    except BaseException as exc:
        record['status'] = 'failed'
        record['error'] = type(exc).__name__+': '+str(exc)
        raise
    finally:
        if database is not None:
            database.close()
        (output/'result.json').write_text(json.dumps(record, indent=2, sort_keys=True)+'\n')
    print(f'{len(record["checks"])} real native query checks passed: {output}/result.json')


if __name__ == '__main__':
    main()
