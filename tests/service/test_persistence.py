"""Real same-executable restarts and deterministic process death / disk errors.

Build the opt-in fault binary with `make test-persistence`. Hooks are absent
from the normal binary. Run this heavy suite under the shared flock.
"""
import hashlib
import os
from pathlib import Path
import shutil
import signal
import socket
import subprocess
import tempfile
import time
import unittest
import zlib

from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_prepared import universal_access_proof
from tools.client import decode, encode, frame, prepared_frame
from applications.tasks.app import prepare

BINARY = Path(os.environ.get('JAYDB_PERSISTENCE_BINARY',
    ROOT/'.build/persistence/fault/release/jaydb2'))
CHECKPOINT_MAGIC = b'jaydb2-wal-checkpoint-v2\n'
SEGMENT_MAGIC = b'jaydb2-wal-segment-v2\n'
SALT_SIZE = 16
CHECKPOINT_LSN_OFFSET = len(CHECKPOINT_MAGIC) + SALT_SIZE
SEGMENT_HEADER_SIZE = len(SEGMENT_MAGIC) + SALT_SIZE + 8 + 4
FRAME_HEADER_SIZE = 8 + 4 + 8
SEGMENT_SIZE = 8 * 1024 * 1024


def numbered(path, prefix):
    return sorted(path.glob(prefix+'-*'), key=lambda file: int(file.name.split('-')[1]))


def wal_records(path):
    def blob(data):
        size = int.from_bytes(data[:8], 'big')
        assert len(data) >= 8 + size
        return data[8:8+size], data[8+size:]

    def optional(data):
        assert data[0] in (0, 1)
        return blob(data[1:]) if data[0] else (None, data[1:])

    for segment in numbered(path, 'segment'):
        data = segment.read_bytes()
        preallocated = len(data) == SEGMENT_SIZE
        header, data = data[:SEGMENT_HEADER_SIZE], data[SEGMENT_HEADER_SIZE:]
        assert header.startswith(SEGMENT_MAGIC)
        assert zlib.crc32(header[:-4]) == int.from_bytes(header[-4:], 'big')
        salt = header[len(SEGMENT_MAGIC):len(SEGMENT_MAGIC)+SALT_SIZE]
        while data:
            size = int.from_bytes(data[:8], 'big')
            if size == 0 and preallocated:
                assert not data.strip(b'\0'), 'nonzero bytes after WAL padding'
                break
            crc = int.from_bytes(data[8:12], 'big')
            tag = hashlib.sha256(b'jaydb2-wal-frame-v2\0' + salt + data[:12]).digest()[:8]
            assert data[12:FRAME_HEADER_SIZE] == tag
            end = FRAME_HEADER_SIZE + size
            payload, data = data[FRAME_HEADER_SIZE:end], data[end:]
            assert len(payload) == size and zlib.crc32(payload) == crc
            while payload:
                lsn = int.from_bytes(payload[:8], 'big')
                assert payload[8] == 1  # These test databases have no migrations.
                count = int.from_bytes(payload[9:17], 'big')
                payload, writes = payload[17:], []
                for _ in range(count):
                    collection, payload = optional(payload)
                    key, payload = blob(payload)
                    row, payload = optional(payload)
                    writes.append((collection.decode() if collection is not None else None,
                                   key.decode(), decode(row) if row is not None else None))
                yield lsn, writes


def state_bytes(path):
    checkpoint = numbered(path, 'checkpoint')[-1].read_bytes()
    checked, crc = checkpoint[:-4], checkpoint[-4:]
    assert checked.startswith(CHECKPOINT_MAGIC) and zlib.crc32(checked) == int.from_bytes(crc, 'big')
    start = CHECKPOINT_LSN_OFFSET
    lsn = int.from_bytes(checked[start:start+8], 'big')
    descriptor_size = int.from_bytes(checked[start+8:start+16], 'big')
    state = decode(checked[start+16+descriptor_size:])
    collections = {table['name']: table['rows'] for table in state['tables']}
    collections[None] = state['users']
    indexed = {collection: {fields['id']: fields for fields in rows}
               for collection, rows in collections.items()}
    for commit_lsn, writes in wal_records(path):
        if commit_lsn <= lsn:
            continue
        assert commit_lsn == lsn + 1
        lsn = commit_lsn
        for collection, key, row in writes:
            if row is None:
                indexed[collection].pop(key, None)
            else:
                indexed[collection][key] = row
    for collection, rows in collections.items():
        rows[:] = [row for _, row in sorted(indexed[collection].items())]
    return encode(state)


class PersistenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not BINARY.is_file():
            raise AssertionError('Run make test-persistence to build the real fault binary')
        cls.temporary = tempfile.TemporaryDirectory(prefix='jaydb-persistence-')
        cls.root = Path(cls.temporary.name)
        cls.folder = ROOT/'examples/access'
        cls.code, cls.proof = ((cls.folder/name).read_text()
                              for name in ('Client.bend', 'ClientProof.bend'))
        cls.base = cls.root/'base'
        server = Server(cls.folder, binary=BINARY, threads=1,
                        arguments=['--storage', str(cls.base), '--storage-mode', 'create'])
        try:
            assert server.call(cls.code, cls.proof, 'invalid')['status'] == 'authentication', server.diagnostics()
            server.finish()
        finally:
            server.close()
        cls.initial = state_bytes(cls.base)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def setUp(self):
        self.directory = Path(tempfile.mkdtemp(dir=self.root))
        self.path = self.directory/'db'
        shutil.copytree(self.base, self.path)

    def server(self, mode='open', env=None, folder=None):
        server = Server(folder or self.folder, binary=BINARY, threads=1, env=env,
            arguments=['--storage', str(self.path), '--storage-mode', mode], seed=mode == 'create')
        self.addCleanup(server.close)
        return server

    def call(self, server, credential='alice-token', arguments=None):
        return server.call(self.code, self.proof, credential, arguments)

    def run_cli(self, *args, binary=BINARY, folder=None):
        return subprocess.run([str(binary), '--configuration', str((folder or self.folder)/'Configuration.bend'),
            '--threads', '1', *map(str, args)], cwd=ROOT, input=b'', capture_output=True, timeout=180)

    def open_failure(self):
        result = self.run_cli('--storage', self.path, '--storage-mode', 'open')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b'')
        return result

    def test_acknowledged_restart_credentials_handles_and_seed_free_open(self):
        server = self.server()
        handle = server.prepared(0, self.code, 'alice-token', proof=universal_access_proof(self.proof))['value']
        self.assertEqual(server.prepared(1, handle, 'alice-token', 'durable'),
                         {'status': 'success', 'value': 'durable'}, server.diagnostics())
        committed = (self.path/'segment-1').read_bytes()
        # The real official worker writes privately, then fails consuming a
        # Nat beyond its immediate representation. It must never enter storage.
        failing = self.code.replace('S.Finish{value}',
            'S.Finish{D.VInt{0, U32.from_nat(Nat.mul(16777216n, 16777216n))}}')
        self.assertNotEqual(failing, self.code)
        self.assertEqual(server.call(failing, self.proof, 'durable', 'never-published'),
                         {'status': 'failure', 'value': None}, server.diagnostics())
        self.assertEqual((self.path/'segment-1').read_bytes(), committed)
        server.finish()
        # Seed disappearance is immaterial: recover stages only configuration.
        local = self.directory/'app'; local.mkdir()
        shutil.copyfile(self.folder/'Configuration.bend', local/'Configuration.bend')
        self.assertFalse((local/'Seed.bend').exists())
        server = self.server(folder=local)
        self.assertEqual(self.call(server), {'status': 'authentication', 'value': None})
        self.assertEqual(self.call(server, 'durable'), {'status': 'refusal', 'value': 'cancelled'})
        self.assertEqual(server.prepared(1, handle, 'durable', 'foreign'), {'status': 'failure', 'value': None})
        self.assertEqual((self.path/'segment-1').read_bytes(), committed)
        self.assertEqual(self.call(server, 'bob-token', 'bob-durable'), {'status': 'success', 'value': 'bob-durable'})
        server.finish()
        # Normal shutdown is unnecessary once the successful response arrived.
        server = self.server()
        self.assertEqual(self.call(server, 'durable', 'last-ack'), {'status': 'success', 'value': 'last-ack'})
        os.kill(server.process.pid, signal.SIGKILL); server.process.wait(timeout=10)
        server = self.server()
        self.assertEqual(self.call(server, 'last-ack'), {'status': 'refusal', 'value': 'cancelled'})
        self.assertEqual(self.call(server, 'bob-durable'), {'status': 'refusal', 'value': 'cancelled'})
        server.finish()

    def test_all_application_tables_and_users_survive(self):
        app = self.directory/'app'; app.mkdir(); prepare(app)
        self.path = self.directory/'tasks'
        server = self.server(mode='create', folder=app)
        code, proof = ((app/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        for owner in ['alice', 'bob']:
            self.assertEqual(server.call(code, proof, owner+'-token', ['save', 'one', owner+' ü', False]),
                             {'status': 'success', 'value': 'one'}, server.diagnostics())
        exact = state_bytes(self.path)
        self.assertEqual(server.call(code, proof, 'alice-token', ['cancel', 'two', 'rollback', True]),
                         {'status': 'refusal', 'value': 'cancelled'})
        self.assertEqual(state_bytes(self.path), exact)
        server.finish()
        (app/'Seed.bend').unlink()
        server = self.server(folder=app)
        # Check actual recovered RAM bytes via the administrator inspector is
        # unnecessary here: current reads require both users and their tables.
        for owner in ['alice', 'bob']:
            self.assertEqual(server.call(code, proof, owner+'-token', ['view', 'one']),
                {'status': 'success', 'value': {'completed': False, 'id': 'one', 'owner': owner, 'title': owner+' ü'}}, server.diagnostics())
        self.assertEqual(state_bytes(self.path), exact)
        server.finish()

    def test_missing_corrupt_or_incompatible_checkpoint_and_descriptor(self):
        path = self.path/'checkpoint-0'
        checkpoint = path.read_bytes()
        (self.path/'.checkpoint.tmp').write_bytes(checkpoint)
        path.unlink()
        self.assertIn(b'no checkpoint', self.open_failure().stderr)
        path.write_bytes(checkpoint[:-1])
        self.assertIn(b'no valid checkpoint', self.open_failure().stderr)
        corrupt = bytearray(checkpoint); corrupt[-10] ^= 1
        path.write_bytes(corrupt)
        self.assertIn(b'no valid checkpoint', self.open_failure().stderr)
        incompatible = bytearray(checkpoint)
        incompatible[CHECKPOINT_LSN_OFFSET+16] ^= 1
        incompatible[-4:] = zlib.crc32(incompatible[:-4]).to_bytes(4, 'big')
        path.write_bytes(incompatible)
        self.assertIn(b'incompatible WAL environment', self.open_failure().stderr)
        external = self.directory/'external-checkpoint'
        external.write_bytes(checkpoint)
        path.unlink(); path.symlink_to(external)
        self.assertIn(b'nonregular', self.open_failure().stderr)
        path.unlink(); path.write_bytes(checkpoint)
        # Same source, different actual executable bytes must not reopen.
        other = self.directory/'other-controller'
        other.write_bytes(BINARY.read_bytes()+b'\x00'); other.chmod(0o700)
        result = self.run_cli('--storage', self.path, '--storage-mode', 'open', binary=other)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b'incompatible WAL environment', result.stderr)
        changed = self.directory/'changed'; changed.mkdir()
        (changed/'Configuration.bend').write_text((self.folder/'Configuration.bend').read_text()+'\n# changed binding\n')
        result = self.run_cli('--storage', self.path, '--storage-mode', 'open', folder=changed)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b'incompatible WAL environment', result.stderr)
        self.assertEqual(path.read_bytes(), checkpoint)

    def test_create_open_policy_and_real_owner_contention(self):
        self.assertNotEqual(self.run_cli('--storage', self.path).returncode, 0)
        result = self.run_cli('--storage', self.path, '--storage-mode', 'open', '--seed', self.directory/'absent')
        self.assertIn(b'--seed is forbidden', result.stderr)
        result = self.run_cli('--storage', self.path, '--storage-mode', 'create', '--seed', self.folder/'Seed.bend')
        self.assertNotEqual(result.returncode, 0)
        server = self.server()
        self.assertEqual(self.call(server)['status'], 'refusal')
        result = self.open_failure()
        self.assertIn(b'lock', result.stderr.lower())
        server.finish()
        # An orphan checkpoint temp never participates in recovery.
        (self.path/'.checkpoint.tmp').write_bytes(b'not a checkpoint')
        server = self.server()
        self.assertEqual(self.call(server)['status'], 'refusal')
        server.finish()

    def test_real_segment_creation_failure_is_fatal(self):
        server = self.server()
        self.assertEqual(self.call(server)['status'], 'refusal')
        segment = self.path/'segment-1'
        segment.mkdir()
        request = frame(dict(code=self.code, proof=self.proof, credential='alice-token',
                             arguments='not-committed'))
        server.process.stdin.write(request)
        server.process.stdin.flush()
        self.assertNotEqual(server.process.wait(timeout=180), 0, server.diagnostics())
        self.assertEqual(server.process.stdout.read(), b'')
        self.assertIn('STORAGE_UNCERTAIN', server.diagnostics())
        segment.rmdir()
        self.assertEqual(state_bytes(self.path), self.initial)
        recovered = self.server()
        self.assertEqual(self.call(recovered, arguments='retry-after-repair'),
                         {'status': 'success', 'value': 'retry-after-repair'})
        recovered.finish()

    def test_many_commits_sigkill_then_checkpoint_and_replay_are_atomic(self):
        from paper.bench.fixtures import bulk_population, package
        app = package(self.directory/'point', 'read', rows=0)
        self.path = self.directory/'point-data'
        code, proof, universal = ((app/name).read_text()
            for name in ('Client.bend', 'ClientProof.bend', 'PreparedProof.bend'))
        populate, certificate = bulk_population(proof)
        server = self.server(mode='create', folder=app)
        receipt = server.prepared(0, populate, 'alice-token', proof=certificate)
        self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
        handle = receipt['value']
        pairs = [[f'key{i:03d}a', f'key{i:03d}b'] for i in range(281)]
        for i, pair in enumerate(pairs[:-1]):
            self.assertEqual(server.prepared(1, handle, 'alice-token', pair),
                             {'status': 'success', 'value': 2*(i+1)}, server.diagnostics())
        deadline = time.monotonic() + 10
        while not (self.path/'checkpoint-256').is_file():
            self.assertLess(time.monotonic(), deadline, 'background checkpoint did not run')
            time.sleep(0.01)
        server.process.stdin.write(prepared_frame(1, handle, 'alice-token', pairs[-1]))
        server.process.stdin.flush()
        os.kill(server.process.pid, signal.SIGKILL)
        server.process.wait(timeout=10)
        server.close()

        reopened = self.server(folder=app)
        receipt = reopened.prepared(0, code, 'alice-token', proof=universal)
        self.assertEqual(receipt['status'], 'prepared', reopened.diagnostics())
        self.assertTrue(any(lsn > 256 for lsn, _ in wal_records(self.path)))
        handle = receipt['value']
        for pair in pairs[:-1]:
            for key in pair:
                self.assertEqual(reopened.prepared(1, handle, 'alice-token', ['read', key]),
                                 {'status': 'success', 'value': 0})
        result = [reopened.prepared(1, handle, 'alice-token', ['read', key]) for key in pairs[-1]]
        self.assertEqual(result[0], result[1], 'the unacknowledged transaction must be atomic')
        self.assertIn(result[0], [{'status': 'success', 'value': 0}, {'status': 'refusal', 'value': None}])
        reopened.finish()

    def test_torn_tail_is_truncated_and_the_next_commit_replays(self):
        server = self.server()
        self.assertEqual(self.call(server, arguments='durable'), {'status': 'success', 'value': 'durable'})
        server.finish()
        segment = self.path/'segment-1'
        image = segment.read_bytes()
        start = SEGMENT_HEADER_SIZE
        end = start + FRAME_HEADER_SIZE + int.from_bytes(image[start:start+8], 'big')
        entire_record = image[:end]
        with segment.open('r+b') as stream:
            # Start the torn record at the logical end, inside any reservation.
            stream.seek(end)
            stream.write(entire_record[start:-5])
        reopened = self.server()
        self.assertEqual(self.call(reopened, 'durable'), {'status': 'refusal', 'value': 'cancelled'})
        self.assertEqual(segment.read_bytes(), entire_record)
        self.assertEqual(self.call(reopened, 'durable', 'after-tail'), {'status': 'success', 'value': 'after-tail'})
        reopened.finish()
        final = self.server()
        self.assertEqual(self.call(final, 'after-tail'), {'status': 'refusal', 'value': 'cancelled'})
        final.finish()

    def run_boundary(self, point, kill, expected_new):
        path = self.directory/point
        shutil.copytree(self.base, path); self.path = path
        env = dict(os.environ, JAYDB_STORAGE_FAULT=point)
        listener = None
        if kill:
            # Independent of the selected fault target directory and of long
            # worktree/TMPDIR paths; each subcase owns its short Unix address.
            gate = self.enterContext(tempfile.TemporaryDirectory(prefix='jaydb-storage-gate-', dir='/tmp'))
            socket_path = Path(gate)/'socket'
            listener = self.enterContext(socket.socket(socket.AF_UNIX))
            listener.bind(str(socket_path)); listener.listen(1); listener.settimeout(180)
            env['JAYDB_STORAGE_BARRIER'] = str(socket_path)
        server = self.server(env=env)
        request = frame(dict(code=self.code, proof=self.proof, credential='alice-token', arguments='new-token'))
        # Queue another request. Fatal commits must never produce its response.
        # Keep the queued frame below pipe capacity: the service may stop
        # reading immediately after the first commit. It would authenticate and
        # respond if dispatched, so zero output checks ordered termination.
        later = frame(dict(code='', proof='', credential='not-a-user', arguments=None))
        server.process.stdin.write(request+later); server.process.stdin.flush()
        if kill:
            try:
                stream, _ = listener.accept()
                with stream:
                    self.assertEqual(stream.recv(128).decode(), point)
                    # Ordinary request workers and staging directories are gone
                    # before the storage protocol is entered.
                    private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
                    self.assertFalse(list(private.glob('request-*')))
                    self.assertFalse(Path(f'/proc/{server.process.pid}/task/{server.process.pid}/children').read_text().strip())
                    os.kill(server.process.pid, signal.SIGKILL)
                    server.process.wait(timeout=10)
            finally:
                listener.close(); socket_path.unlink(missing_ok=True)
            self.assertEqual(server.process.stdout.read(), b'')
        else:
            self.assertNotEqual(server.process.wait(timeout=180), 0, server.diagnostics())
            self.assertEqual(server.process.stdout.read(), b'')
            self.assertIn('STORAGE_UNCERTAIN', server.diagnostics())
        recovered = self.server()
        credential = 'new-token' if expected_new else 'alice-token'
        self.assertEqual(self.call(recovered, credential), {'status': 'refusal', 'value': 'cancelled'}, recovered.diagnostics())
        self.assertEqual(self.call(recovered, 'bob-token'), {'status': 'refusal', 'value': 'cancelled'})
        recovered.finish()
        if not expected_new:
            self.assertEqual(state_bytes(self.path), self.initial)

    def test_process_death_at_wal_boundaries(self):
        for point, new in [('wal_before_write', False), ('before_publish', True),
                           ('after_publish', True)]:
            with self.subTest(point=point):
                self.run_boundary(point, kill=True, expected_new=new)

    def test_wal_errors_stop_without_a_rollback_response(self):
        # Before fdatasync, a complete record can still survive process exit.
        for point, new in [('wal_before_write', False), ('wal_before_sync', True)]:
            with self.subTest(point=point):
                self.run_boundary(point, kill=False, expected_new=new)


if __name__ == '__main__':
    unittest.main(verbosity=2)
