#!/usr/bin/env python3
"""Certified ordinary-table indexes on the combined host, across durable reopen.

Run under the common heavy lock after building this checkout. This reuses the
indexed application's actual laws and certificate; it does not invent a shared
index/receipt schema or claim that two applications' invariants compose.
"""
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from applications.indexed import check, negative_cases
from tests.service.test_end_to_end import Server
from tests.service.test_persistence import state_bytes
from tools.client import decode

BUILD = ROOT / 'build/integration/features'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def state(path, alice, bob):
    """Independent decoded-state oracle, including exact derived entries."""
    saved = state_bytes(path)
    value = decode(saved)
    tables = {table['name']: table['rows'] for table in value['tables']}
    assert set(tables) == {'alice', 'alice_index', 'bob', 'bob_index'}, tables
    for owner, available in (('alice', alice), ('bob', bob)):
        assert tables[owner] == [dict(available=available, id='item')], tables
        # Key.encode([tag]) tags every scalar, terminates the component, then
        # terminates the tuple. This independent Python construction checks the
        # actual saved value, rather than trusting a query of the same helper.
        tag = 'ready' if available else 'busy'
        key = 'p' + ''.join('c' + scalar for scalar in tag) + 'ez'
        assert tables[owner + '_index'] == [dict(id='item', target='item', value=key)], tables
    assert value['users'] == [dict(credential=owner + '-token', id=owner, kind='user')
                             for owner in ('alice', 'bob')], value['users']
    return saved


def universal(proof):
    old = '''def B.certificate(s,valid,identity,n):
  +s=s
  certify(I.context(),I.arguments(),B.code(),n,s,initial(s,valid))'''
    new = '''def B.certificate(ctx,args,s,valid,identity,n):
  +s=s
  certify(ctx,args,B.code(),n,s,initial(s,valid))'''
    assert proof.count(old) == 1
    # Only instantiate the existing arbitrary-context/argument theorem at the
    # prepared protocol's universal target. The host checks this actual proof.
    return proof.replace(old, new)


@contextmanager
def session(app, storage, mode, log):
    server = Server(app, threads=2, seed=mode == 'create',
        env=dict(os.environ, TMPDIR=str(BUILD), BENDRTS='--gpu-build --help'),
        arguments=['--storage', str(storage), '--storage-mode', mode,
                   '--timing-log', str(log)])
    try:
        yield server
        server.finish()
    finally:
        diagnostics = server.diagnostics()
        (BUILD / (mode + '-host.log')).write_text(diagnostics)
        server.close()


def timing(log, principals):
    records = [json.loads(line) for line in log.read_text().splitlines()]
    assert len(records) == len(principals), (records, principals)
    assert [record['sequence'] for record in records] == list(range(1, len(records) + 1)), records
    assert [record['principal'] for record in records] == principals, records
    for record in records:
        assert record['format'] == 'jaydb-service-timing-v1', record
        assert record['elapsed_ns'].isdigit() and int(record['elapsed_ns']) > 0, record
        assert 'quota' not in record, record
    return records


def main():
    BUILD.mkdir(parents=True, exist_ok=True)
    binary = ROOT / 'target/release/jaydb2'
    identity = digest(binary)
    evidence = {'controller_sha256': identity, 'threads': 2,
                'scope': 'certified indexed application, durable snapshots and administrator timing',
                'source_sha256': {name: digest(ROOT / name) for name in
                    ('server/main.rs', 'server/capture.rs', 'server/storage.rs',
                     'server/timing.rs', 'src/Messages.bend')},
                'sessions': []}
    with tempfile.TemporaryDirectory(prefix='indexed-', dir=BUILD) as temporary:
        directory = Path(temporary)
        app = directory / 'app'
        check.prepare(app)
        code = (app / 'Client.bend').read_text()
        proof = (app / 'ClientProof.bend').read_text()
        prepared_proof = universal(proof)
        storage = directory / 'db'
        create_log, open_log = directory / 'create.ndjson', directory / 'open.ndjson'
        actors = []
        with session(app, storage, 'create', create_log) as server:
            receipt = server.prepared(0, code, 'alice-token', proof=prepared_proof)
            assert receipt['status'] == 'prepared', (receipt, server.diagnostics())
            handle = receipt['value']
            actors.append('alice')

            def call(owner, args, expected):
                result = server.prepared(1, handle, owner + '-token', args)
                assert result == dict(status='success', value=expected), (args, result, server.diagnostics())
                actors.append(owner)

            call('alice', ['query', False], ['item'])
            call('bob', ['query', False], ['item'])
            call('alice', ['set', True], True)
            call('bob', ['set', True], True)
            call('bob', ['set', False], False)
            call('alice', ['rebuild'], 'rebuilt')
            call('alice', ['query', True], ['item'])
            call('bob', ['query', False], ['item'])
            saved = state(storage, True, False)
        create_records = timing(create_log, actors)
        evidence['sessions'].append(dict(mode='create', requests=len(actors),
            state_sha256=hashlib.sha256(saved).hexdigest(), timing=create_records))
        (app / 'Seed.bend').unlink()
        actors = []
        with session(app, storage, 'open', open_log) as server:
            result = server.prepared(1, handle, 'alice-token', ['query', True])
            assert result == dict(status='failure', value=None), result
            actors.append('alice')
            receipt = server.prepared(0, code, 'alice-token', proof=prepared_proof)
            assert receipt['status'] == 'prepared', (receipt, server.diagnostics())
            handle = receipt['value']
            actors.append('alice')
            call('alice', ['query', True], ['item'])
            call('alice', ['query', False], [])
            call('bob', ['query', False], ['item'])
            for kind, args in (('omitted', ['set', False]), ('forged', ['set', False]),
                               ('forbidden', ['query', True])):
                bad_code, bad_proof = negative_cases.variant(kind)
                before = state_bytes(storage)
                result = server.call(bad_code, bad_proof, 'alice-token', args)
                assert result == dict(status='certificate', value=None), (kind, result, server.diagnostics())
                actors.append('alice')
                assert state_bytes(storage) == before == saved, kind
                call('alice', ['query', True], ['item'])
                call('bob', ['query', False], ['item'])
            call('alice', ['rebuild'], 'rebuilt')
            call('bob', ['rebuild'], 'rebuilt')
            assert state(storage, True, False) == saved
        open_records = timing(open_log, actors)
        evidence['sessions'].append(dict(mode='open', seed_present=False,
            requests=len(actors), state_sha256=hashlib.sha256(saved).hexdigest(), timing=open_records))
    assert digest(binary) == identity, 'controller changed during this gate'
    (BUILD / 'result.json').write_text(json.dumps(evidence, indent=2) + '\n')
    print('PASS combined host: certified index maintenance/rebuild, seed-free durable reopen, '
          'ephemeral handles, three real certificate denials without publication, exact saved '
          'business/index/user rows, administrator timing and exclusive write-capable handles.', flush=True)


if __name__ == '__main__':
    main()
