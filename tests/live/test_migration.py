"""Exercise checked whole-state migrations standalone and on a live service."""

from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager

from copy import deepcopy
import json
import os
import socket
import stat
from pathlib import Path
import subprocess
import tempfile
from threading import Barrier, Event
from time import monotonic, sleep
import unittest

from applications.tasks.app import prepare
from tests.live.test_concurrency import exchange
from tests.service.test_end_to_end import Server
from tools.client import decode, encode, prepared_frame, unframe


ROOT = Path(__file__).resolve().parents[2]
EXAMPLE = ROOT / 'applications/tasks/migrations'
LOCK = json.loads((ROOT / 'tools/admission/toolchain.lock.json').read_text())
TOOLCHAIN = (
    ROOT / '.tools' / ('bend-source-' + LOCK['version']),
    ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256']),
)
OLD_STATE = {
    'tables': [
        {'name': 'alice', 'rows': [
            {'completed': False, 'id': 'a1', 'owner': 'alice', 'title': 'Buy bread'},
            {'completed': True, 'id': 'a2', 'owner': 'alice', 'title': 'Call Zoë'},
        ]},
        {'name': 'bob', 'rows': [
            {'completed': False, 'id': 'b1', 'owner': 'bob', 'title': 'Review report'},
        ]},
    ],
    'users': [
        {'credential': 'alice-token', 'id': 'alice', 'kind': 'user'},
        {'credential': 'bob-token', 'id': 'bob', 'kind': 'user'},
    ],
}


class MigrationTest(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory(prefix='jaydb-migrate-')
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        old = self.root / 'old-app'
        new = self.root / 'new-app'
        for folder in (old, new):
            folder.mkdir()
            prepare(folder)
        # The two administrator graphs may reuse a helper filename with different bytes.
        policy = new / 'Policy.bend'
        policy.write_text(policy.read_text() + '\ndef version() -> Nat:\n  2n\n')
        self.old = old / 'Configuration.bend'
        self.new = new / 'Configuration.bend'
        self.new.write_bytes((EXAMPLE / 'Configuration.bend').read_bytes())
        self.migration = (EXAMPLE / 'Migration.bend').read_text()

    def build(self, name, source, *, old=None):
        module = self.root / (name + '.bend')
        module.write_text(source)
        output = self.root / name
        result = subprocess.run(
            ['node', '--stack_size=65536', 'tools/service/stage.mjs', 'migrate',
             output, old or self.old, self.new, module, *TOOLCHAIN],
            cwd=ROOT, capture_output=True, text=True, timeout=180,
        )
        return result, output / 'migrate'

    def admitted(self, name, source, *, old=None):
        result, artifact = self.build(name, source, old=old)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads((artifact / 'checked.c.json').read_text())['admission']
        self.assertTrue(report['primary'])
        self.assertTrue(report['bendtt'])
        self.assertEqual(report['kernel']['primitives'], ['Native:read', 'Native:write'])
        return json.loads(result.stdout), artifact

    def run_migration(self, program, canonical_state):
        result = subprocess.run(
            [program, '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
            cwd=ROOT, input=canonical_state, capture_output=True, timeout=20,
            env={**os.environ, 'BENDRTS': ''},
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def test_rows_are_preserved_and_decode_under_new_schema(self):
        built, artifact = self.admitted('success', self.migration)
        self.assertIn('def version()', (artifact / 'Policy.bend').read_text())
        self.assertNotIn('def version()', (artifact / 'Old/Policy.bend').read_text())

        expected = deepcopy(OLD_STATE)
        for table in expected['tables']:
            for row in table['rows']:
                row['priority'] = None
        result = self.run_migration(built['program'], encode(OLD_STATE))
        self.assertEqual(result[:1], b'\x01')
        self.assertEqual(decode(result[1:]), expected)
        self.assertEqual(result[1:], encode(expected))
        self.assert_error(self.run_migration(built['program'], result[1:]), 'failure')

        # Feed the proposal back through the checked decoder using the frozen
        # new environment. Use a ceiling equal to the canonical proposal size.
        self.new.write_text(self.new.read_text().replace('65536n', f'{len(result) - 1}n').replace(
            'Policy.config(schema(), limits(), environment())',
            'S.Configuration{schema(), S.NoneLaw{}, limits(), environment()}',
        ))
        identity = '''import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Old/Configuration.bend as Old

def migrate(s: D.State) -> D.State:
  s

def preserves(s: D.State, valid: R.Valid(Old.config(), s)) -> Unit:
  Unit{}
'''
        checked, _ = self.admitted('redecode', identity, old=built['newEnvironment'])
        self.assertEqual(self.run_migration(checked['program'], result[1:]), result)

        expected['tables'][0]['rows'][0]['title'] += '!'
        self.assert_error(self.run_migration(checked['program'], encode(expected)), 'limit')

    @contextmanager
    def connection(self, server, path):
        with socket.socket(socket.AF_UNIX) as stream:
            stream.settimeout(180)
            deadline = monotonic() + 180
            while True:
                try:
                    stream.connect(str(path))
                    break
                except (FileNotFoundError, ConnectionRefusedError):
                    if server.process.poll() is not None or monotonic() >= deadline:
                        self.fail(f'{path} did not open\n{server.diagnostics()}')
                    sleep(0.025)
            yield stream

    def service(self, name, configuration, mode):
        endpoint = self.root / f'{name}.sock'
        admin = self.root / f'{name}-admin.sock'
        server = Server(configuration.parent, seed=mode == 'create', threads=1,
                        env=dict(os.environ, TMPDIR=str(self.root)), arguments=[
                            '--listen', str(endpoint), '--admin-socket', str(admin),
                            '--concurrency', '4', '--storage', str(self.root / 'db'),
                            '--storage-mode', mode,
                        ])
        self.addCleanup(server.close)
        return server, endpoint, admin

    def program(self, *, with_priority=False):
        code = self.old.with_name('Client.bend').read_text()
        proof = self.old.with_name('ClientProof.bend').read_text().replace(
            'def B.certificate(s, valid, identity, n):\n'
            '  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)',
            'def B.certificate(ctx, args, s, valid, identity, n):\n'
            '  certify(ctx, args, B.code(), s, valid, identity, n)',
        )
        if with_priority:
            code = code.replace('D.Field{"title", D.VText{title}}]',
                                'D.Field{"priority", D.VInt{0, 7}}, D.Field{"title", D.VText{title}}]')
            code = code.replace('id, "completed"}, detail(', 'id, "priority"}, detail(')
            start = code.index('    case S.Datum{D.Cell{D.VBool{done}}}:')
            end = code.index('    case _: D.VAbsent{}', start)
            code = code[:start] + '    case S.Datum{D.Cell{value}}: value\n' + code[end:]
        return code, proof

    def prepare_client(self, server, stream, *, with_priority=False):
        code, proof = self.program(with_priority=with_priority)
        reply = exchange(stream, prepared_frame(0, code, 'alice-token', proof=proof))
        self.assertEqual(reply['status'], 'prepared', server.diagnostics())
        return reply['value']

    def call(self, stream, handle, args):
        return exchange(stream, prepared_frame(1, handle, 'alice-token', args))

    def migrate(self, server, endpoint, source, *, started=None):
        module = self.root / 'RunMigration.bend'
        module.write_text(source)
        with self.connection(server, endpoint) as stream, stream.makefile('rb') as reply:
            self.assertEqual(stat.S_IMODE(endpoint.stat().st_mode), 0o600)
            stream.sendall(json.dumps({'command': 'migrate', 'configuration': str(self.new),
                                       'migration': str(module)}).encode() + b'\n')
            if started is not None:
                started.set()
            result = json.loads(reply.readline())
            self.assertEqual(reply.read(), b'')
            return result

    def test_online_migration_retires_handles_and_recovers_concurrent_writes(self):
        # A connection waiting for the next header must use the new message limit.
        self.new.write_text(self.new.read_text().replace('S.Limits{32768n,', 'S.Limits{65536n,'))
        server, endpoint, admin = self.service('create', self.old, 'create')
        with self.connection(server, endpoint) as stream:
            old_handle = self.prepare_client(server, stream)
            saved = self.call(stream, old_handle, ['save', 'first', 'Buy bread', False])
            self.assertEqual(saved, {'status': 'success', 'value': 'first'})
            self.assertEqual(self.call(stream, old_handle, ['view', 'first'])['value']['title'],
                             'Buy bread')

            clients = 3
            ready = Barrier(clients + 1, timeout=180)
            submitted = Event()

            def write_until_retired(lane):
                acknowledged = set()
                with self.connection(server, endpoint) as writer:
                    ready.wait()
                    self.assertTrue(submitted.wait(180))
                    deadline = monotonic() + 180
                    for index in range(10000):
                        # Keep racing with reads after creating a bounded set of unique rows.
                        key = f'lane-{lane}-{index}'
                        writing = index < 40
                        args = ['save', key, key, False] if writing else ['view', 'first']
                        result = self.call(writer, old_handle, args)
                        if result == {'status': 'failure', 'value': None}:
                            self.assertEqual(self.call(writer, old_handle, ['list']), result)
                            return acknowledged
                        if writing:
                            self.assertEqual(result, {'status': 'success', 'value': key})
                            acknowledged.add(key)
                        else:
                            self.assertEqual(result, {'status': 'success', 'value': {
                                'completed': False, 'id': 'first', 'owner': 'alice', 'title': 'Buy bread'}})
                        self.assertLess(monotonic(), deadline, 'old handle was never retired')
                        sleep(0.05)
                self.fail('old handle was never retired')

            with ThreadPoolExecutor(clients + 1) as pool:
                writers = [pool.submit(write_until_retired, lane) for lane in range(clients)]
                ready.wait()
                migration = pool.submit(self.migrate, server, admin, self.migration,
                                        started=submitted)
                result = migration.result(timeout=180)
                self.assertEqual(result['status'], 'success', (result, server.diagnostics()))
                keys = set().union(*(writer.result(timeout=180) for writer in writers))
            self.assertTrue(all(any(key.startswith(f'lane-{lane}-') for key in keys)
                                for lane in range(clients)), keys)
            self.assertEqual(result['lsn'], len(keys) + 2)
            self.assertEqual(self.call(stream, old_handle, ['list']),
                             {'status': 'failure', 'value': None})
            self.assertIn('HANDLE: unknown or invalidated handle', server.diagnostics())
            large_invalid = b'\0' * 32769
            self.assertEqual(exchange(stream, len(large_invalid).to_bytes(8, 'big') + large_invalid),
                             {'status': 'input', 'value': None})

            new_handle = self.prepare_client(server, stream, with_priority=True)
            self.assertNotEqual(new_handle, old_handle)
            self.assertEqual(self.call(stream, new_handle, ['view', 'first']),
                             {'status': 'success', 'value': None})
            self.assertEqual(self.call(stream, new_handle, ['save', 'later', 'New shape', False]),
                             {'status': 'success', 'value': 'later'})
            self.assertEqual(self.call(stream, new_handle, ['view', 'later']),
                             {'status': 'success', 'value': 7})

            legacy_shape = self.prepare_client(server, stream)
            self.assertEqual(self.call(stream, legacy_shape, ['save', 'bad', 'Old shape', False]),
                             {'status': 'data', 'value': None})
            self.assertEqual(self.call(stream, legacy_shape, ['view', 'first']),
                             {'status': 'success', 'value': {
                                 'completed': False, 'id': 'first', 'owner': 'alice', 'title': 'Buy bread'}})
        server.process.kill()
        server.process.wait(timeout=10)

        refused, _, _ = self.service('old', self.old, 'open')
        self.assertEqual(refused.process.wait(timeout=180), 1, refused.diagnostics())
        self.assertIn('incompatible WAL environment descriptor', refused.diagnostics())

        # SIGKILL left both socket paths behind. Reuse them on recovery.
        recovered, endpoint, _ = self.service('create', self.new, 'open')
        with self.connection(recovered, endpoint) as stream:
            handle = self.prepare_client(recovered, stream, with_priority=True)
            self.assertEqual(self.call(stream, handle, ['list']),
                             {'status': 'success', 'value': sorted(keys | {'first', 'later'})})
            self.assertEqual(self.call(stream, handle, ['view', 'first']),
                             {'status': 'success', 'value': None})
            self.assertEqual(self.call(stream, handle, ['view', 'later']),
                             {'status': 'success', 'value': 7})

    def test_runtime_rejection_preserves_the_old_service(self):
        server, endpoint, admin = self.service('create', self.old, 'create')
        with self.connection(server, endpoint) as stream:
            handle = self.prepare_client(server, stream)
            self.assertEqual(self.call(stream, handle, ['save', 'first', 'Buy bread', False]),
                             {'status': 'success', 'value': 'first'})
            invalid = self.migration.replace('D.Field{"priority", D.VAbsent{}}',
                                             'D.Field{"priority", D.VBool{True{}}}')
            result = self.migrate(server, admin, invalid)
            self.assertEqual(result, {'status': 'error', 'code': 'data',
                                      'message': 'migration returned data'})
            self.assertEqual(self.call(stream, handle, ['save', 'second', 'Call Zoë', True]),
                             {'status': 'success', 'value': 'second'})
            self.assertEqual(self.call(stream, handle, ['list']),
                             {'status': 'success', 'value': ['first', 'second']})
        server.process.kill()
        server.process.wait(timeout=10)
        recovered, endpoint, _ = self.service('old', self.old, 'open')
        with self.connection(recovered, endpoint) as stream:
            handle = self.prepare_client(recovered, stream)
            self.assertEqual(self.call(stream, handle, ['list']),
                             {'status': 'success', 'value': ['first', 'second']})

    def assert_error(self, result, status):
        self.assertEqual(result[:1], b'\x00')
        self.assertEqual(unframe(result[1:]), {'status': status, 'value': None})

    def test_bad_structure_is_rejected_after_admission(self):
        invalid = self.migration.replace('D.Field{"priority", D.VAbsent{}}',
                                         'D.Field{"priority", D.VBool{True{}}}')
        built, _ = self.admitted('bad-structure', invalid)
        self.assert_error(self.run_migration(built['program'], encode(OLD_STATE)), 'data')

    def test_invalid_proof_is_rejected_at_admission(self):
        invalid = self.migration[:self.migration.index('law preserves:')] + '''
def preserves(s: D.State, valid: R.Valid(Old.config(), s)) -> Unit:
  Unit{}
'''
        result, artifact = self.build('bad-proof', invalid)
        self.assertEqual(result.returncode, 2)
        self.assertIn('"code":"PRIMARY_CHECK"', result.stderr)
        self.assertIn('migration_preserves_laws', result.stderr)
        self.assertFalse(list(artifact.glob('*.program')))


if __name__ == '__main__':
    unittest.main()
