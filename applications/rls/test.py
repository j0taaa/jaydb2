#!/usr/bin/env python3
"""RLS through the real native host and standard framed ordinary/prepared API."""
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
    old = 'def B.certificate(s, valid, identity, n):'
    assert proof.count(old) == 1
    # The proof already quantifies over context/arguments; bind the universal
    # admission target exactly as in tests/service/test_prepared.py.
    return proof.replace(old, 'def B.certificate(ctx, args, s, valid, identity, n):\n  +ctx = ctx\n  +args = args') \
                .replace('I.context()', 'ctx').replace('I.arguments()', 'args')


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
                expect(server.call(code, proof, user + '-token', args), status, note_value(user, args, value))

            def note_value(user, args, value):
                if value is not None and args[0] in ('read', 'view'):
                    key = args[1] if args[0] == 'read' else user + ('/2' if args[1] else '/1')
                    return dict(id=key, owner=key.split('/')[0], text=value)
                return value

            # At least one ordinary full certificate is actually admitted,
            # compiled, executed and published before universal preparation.
            call('alice', ['save', False, 'Alice original'], 'alice/1')
            call('alice', ['view', False], 'Alice original')
            call('bob', ['save', False, 'Bob private'], 'bob/1')
            receipt = server.prepared(0, code, 'alice-token', proof=universal_proof())
            assert receipt['status'] == 'prepared', (receipt, server.diagnostics())
            handle = receipt['value']
            assert re.fullmatch(r'[0-9a-f]{64}', handle), handle

            def prepared(user, args, value=None, status='success'):
                expected = note_value(user, args, value) if status == 'success' else value
                expect(server.prepared(1, handle, user + '-token', args), status, expected)

            prepared('alice', ['list'], ['alice/1'])
            prepared('bob', ['list'], ['bob/1'])
            prepared('admin', ['read', 'alice/1'], 'Alice original')
            prepared('admin', ['read', 'bob/1'], 'Bob private')
            prepared('admin', ['count'], 2)
            # Validate every row's existence/payload before and after EACH
            # denial. The stable law fixes owner==key prefix, so this snapshot
            # covers the complete application state (including absent slots).
            def snapshot():
                prepared('alice', ['list'], ['alice/1'])
                prepared('bob', ['list'], ['bob/1'])
                prepared('admin', ['count'], 2)
                prepared('admin', ['read', 'alice/1'], 'Alice original')
                prepared('admin', ['read', 'alice/2'], None)
                prepared('admin', ['read', 'bob/1'], 'Bob private')
                prepared('admin', ['read', 'bob/2'], None)

            snapshot()
            for name, bad_code, bad_proof, _ in cases():
                before = server.diagnostics()
                expect(server.call(bad_code, bad_proof, 'alice-token', ['list']), 'certificate', None)
                delta = server.diagnostics()[len(before):]
                assert 'PRIMARY_CHECK' in delta and 'Location: false' in delta, (name, delta)
                assert '- expected :' in delta and '- observed :' in delta, delta
                snapshot()
                print(f'OK native {name}: admission refusal and complete unchanged application state', flush=True)

            # Fresh state and caller at each use of the SAME prepared artifact.
            prepared('alice', ['save', False, 'Alice updated'], 'alice/1')
            prepared('alice', ['save', True, 'Alice second'], 'alice/2')
            prepared('alice', ['list'], ['alice/1', 'alice/2'])
            prepared('alice', ['view', False], 'Alice updated')
            prepared('bob', ['view', False], 'Bob private')
            prepared('bob', ['save', True, 'Bob second'], 'bob/2')
            prepared('bob', ['list'], ['bob/1', 'bob/2'])
            prepared('admin', ['count'], 4)
            prepared('alice', ['cancel', False, 'discard'], 'cancelled', 'refusal')
            prepared('alice', ['view', False], 'Alice updated')
            prepared('admin', ['read', 'alice/2'], 'Alice second')
            prepared('admin', ['read', 'bob/2'], 'Bob second')
            prepared('alice', ['remove', False], 'alice/1')
            prepared('alice', ['view', False], None)
            prepared('alice', ['list'], ['alice/2'])
            prepared('bob', ['remove', True], 'bob/2')
            prepared('bob', ['list'], ['bob/1'])
            prepared('admin', ['count'], 2)
            prepared('alice', ['remove', True], 'alice/2')
            prepared('alice', ['list'], [])
            prepared('admin', ['count'], 1)
            prepared('admin', ['save', False, 'no admin writes'], 'administrator read or count required', 'refusal')
            prepared('alice', ['count'], 'ordinary command required', 'refusal')
            prepared('alice', ['read', 'bob/1'], 'ordinary command required', 'refusal')
            expect(server.prepared(1, handle, 'invalid-token', ['list']), 'authentication', None)
            expect(server.prepared(2, handle, 'admin-token'), 'invalidated', None)
            server.finish()
            (BUILD / 'host.log').write_text(server.diagnostics())
            assert server.diagnostics().count('PRIMARY_CHECK') == 5, server.diagnostics()
        finally:
            (BUILD / 'host.log').write_text(server.diagnostics())
            server.close()
    print(f'OK native RLS session: {calls} checked responses; ordinary and prepared CRUD, private listings, explicit admin reads/counts, five causal admission denials, rollback and authentication', flush=True)


if __name__ == '__main__':
    native_session()
