#!/usr/bin/env python3
"""Unbounded RLS notes through the real native host, ordinary and prepared."""
from pathlib import Path
import os
import re
import sys
import tempfile

from check import APP, BUILD, ROOT, prepare
sys.path.insert(0, str(ROOT))
from tests.service.test_end_to_end import Server
from negative_cases import cases


def universal_proof():
    proof = (APP / 'ClientProof.bend').read_text()
    old = 'def B.certificate(s, valid, identity, n):\n  certificate(I.context(), I.arguments(), B.code(), s, valid, identity, n)'
    assert proof.count(old) == 1
    # The proof already quantifies over context/arguments; bind the universal
    # admission target exactly as in tests/service/test_prepared.py.
    return proof.replace(old, 'def B.certificate(ctx, args, s, valid, identity, n):\n'
                         '  certificate(ctx, args, B.code(), s, valid, identity, n)')


def note(key, text):
    return dict(id=key, text=text)


def native_session():
    BUILD.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='session-', dir=BUILD) as tmp:
        directory = Path(tmp)
        prepare(directory)
        server = Server(directory, threads=1, env=dict(os.environ, TMPDIR=str(BUILD)))
        code = (directory / 'Client.bend').read_text()
        proof = (directory / 'ClientProof.bend').read_text()
        calls = 0
        try:
            def expect(actual, status, value):
                nonlocal calls
                calls += 1
                assert actual == dict(status=status, value=value), (actual, status, value, server.diagnostics())

            def call(user, args, value=None, status='success'):
                expect(server.call(code, proof, user + '-token', args), status, value)

            # Ordinary full certificates are admitted, executed and published.
            call('alice', ['create', 'first'], 'alice/00000001')
            call('alice', ['list'], [note('alice/00000001', 'first')])
            receipt = server.prepared(0, code, 'alice-token', proof=universal_proof())
            assert receipt['status'] == 'prepared', (receipt, server.diagnostics())
            handle = receipt['value']
            assert re.fullmatch(r'[0-9a-f]{64}', handle), handle

            def prepared(user, args, value=None, status='success'):
                expect(server.prepared(1, handle, user + '-token', args), status, value)

            # The SAME prepared artifact creates and lists with fresh state each use.
            alice = {'alice/00000001': 'first'}
            for i in range(2, 7):
                key = f'alice/{i:08d}'
                prepared('alice', ['create', f'note {i}'], key)
                alice[key] = f'note {i}'
            bob = {}
            for i in (1, 2):
                prepared('bob', ['create', f'bob {i}'], f'bob/{i:08d}')
                bob[f'bob/{i:08d}'] = f'bob {i}'

            def listing(user, rows):
                prepared(user, ['list'], [note(k, rows[k]) for k in sorted(rows)])

            listing('alice', alice)
            listing('bob', bob)
            prepared('admin', ['count'], len(alice) + len(bob))
            prepared('alice', ['view', 'alice/00000003'], note('alice/00000003', 'note 3'))
            prepared('alice', ['update', 'alice/00000003', 'third, edited'], 'alice/00000003')
            alice['alice/00000003'] = 'third, edited'
            prepared('alice', ['view', 'alice/00000003'], note('alice/00000003', 'third, edited'))
            for key in ('alice/00000002', 'alice/00000005'):
                prepared('alice', ['remove', key], key)
                del alice[key]
            listing('alice', alice)
            call('alice', ['list'], [note(k, alice[k]) for k in sorted(alice)])
            prepared('alice', ['view', 'alice/00000002'], None)
            prepared('alice', ['create', 'seventh'], 'alice/00000007')
            alice['alice/00000007'] = 'seventh'
            listing('alice', alice)
            prepared('bob', ['remove', 'bob/00000002'], 'bob/00000002')
            del bob['bob/00000002']
            listing('bob', bob)
            # Removing the largest id makes it available for different content.
            prepared('bob', ['view', 'bob/00000002'], None)
            prepared('bob', ['create', 'replacement bob 2'], 'bob/00000002')
            bob['bob/00000002'] = 'replacement bob 2'
            prepared('bob', ['view', 'bob/00000002'], note('bob/00000002', 'replacement bob 2'))
            listing('bob', bob)

            def snapshot():
                listing('alice', alice)
                listing('bob', bob)
                prepared('admin', ['count'], len(alice) + len(bob))
                for key in [f'alice/{i:08d}' for i in range(1, 9)] + [f'bob/{i:08d}' for i in range(1, 4)]:
                    rows = alice if key.startswith('alice/') else bob
                    prepared('admin', ['read', key], note(key, rows[key]) if key in rows else None)

            snapshot()
            # Runtime refusals by the certified program, not admission failures.
            prepared('alice', ['view', 'bob/00000001'], 'no such own note', 'refusal')
            prepared('alice', ['update', 'bob/00000001', 'x'], 'no such own note', 'refusal')
            prepared('alice', ['remove', 'bob/00000001'], 'no such own note', 'refusal')
            prepared('alice', ['update', 'alice/00000002', 'gone'], 'no such own note', 'refusal')
            prepared('alice', ['cancel', 'discard'], 'cancelled', 'refusal')
            prepared('admin', ['create', 'no admin writes'], 'unsupported', 'refusal')
            prepared('alice', ['count'], 'unsupported', 'refusal')
            prepared('alice', ['read', 'bob/00000001'], 'unsupported', 'refusal')
            snapshot()
            for name, bad_code, bad_proof, _, context in cases():
                before = server.diagnostics()
                expect(server.call(bad_code, bad_proof, context[0] + '-token', ['list']), 'certificate', None)
                delta = server.diagnostics()[len(before):]
                assert 'PRIMARY_CHECK' in delta and 'Location: false' in delta, (name, delta)
                assert '- expected :' in delta and '- observed :' in delta, delta
                snapshot()
                print(f'OK native {name}: admission refusal and complete unchanged application state', flush=True)
            for key in sorted(alice):
                prepared('alice', ['remove', key], key)
            prepared('alice', ['list'], [])
            prepared('admin', ['count'], len(bob))
            expect(server.prepared(1, handle, 'invalid-token', ['list']), 'authentication', None)
            expect(server.prepared(2, handle, 'admin-token'), 'invalidated', None)
            server.finish()
            (BUILD / 'host.log').write_text(server.diagnostics())
            assert server.diagnostics().count('PRIMARY_CHECK') == len(list(cases())), server.diagnostics()
        finally:
            (BUILD / 'host.log').write_text(server.diagnostics())
            server.close()
    print(f'OK native RLS session: {calls} checked responses; ordinary and prepared create/list/view/update/remove '
          f'beyond any fixed slot count, admin reads/counts, {len(list(cases()))} admission denials, rollback and authentication', flush=True)


if __name__ == '__main__':
    native_session()
