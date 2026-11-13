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
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_prepared import universal_access_proof
from tools.client import frame, prepared_frame, unframe
from applications.tasks.app import prepare

BINARY = Path(os.environ.get('JAYDB_PERSISTENCE_BINARY',
    ROOT/'.build/persistence/fault/release/jaydb2'))
MAGIC = b'jaydb2-image-v1\n'
OVERHEAD = len(MAGIC) + 64 + 32 + 32


def state_bytes(path):
    image = (path/'snapshot').read_bytes()
    size = len(image)//2
    candidates = []
    for index in range(2):
        slot = image[index*size:(index+1)*size]
        if slot[:16] != b'jaydb2-slot-v2!!': continue
        length = int.from_bytes(slot[24:32], 'big')
        payload = slot[64:64+length]
        if hashlib.sha256(slot[:32]+payload).digest() != slot[32:64]: continue
        assert hashlib.sha256(payload[:-32]).digest() == payload[-32:]
        assert payload.startswith(MAGIC)
        sequence = int.from_bytes(slot[16:24], 'big')
        assert sequence % 2 == index
        candidates.append((sequence, payload))
    assert candidates
    return max(candidates)[1][OVERHEAD-32:-32]


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

    def server(self, mode='open', env=None, folder=None, repair=False):
        server = Server(folder or self.folder, binary=BINARY, threads=1, env=env,
            arguments=['--storage', str(self.path), '--storage-mode', mode] + (['--repair-invalid-slot'] if repair else []), seed=mode == 'create')
        self.addCleanup(server.close)
        return server

    def call(self, server, credential='alice-token', arguments=None):
        return server.call(self.code, self.proof, credential, arguments)

    def run_cli(self, *args, binary=BINARY, folder=None):
        return subprocess.run([str(binary), '--configuration', str((folder or self.folder)/'Configuration.bend'),
            '--threads', '1', *map(str, args)], cwd=ROOT, input=b'', capture_output=True, timeout=180)

    def open_failure(self, *args):
        result = self.run_cli('--storage', self.path, '--storage-mode', 'open', *args)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b'')
        return result

    def test_acknowledged_restart_credentials_handles_and_seed_free_open(self):
        server = self.server()
        handle = server.prepared(0, self.code, 'alice-token', proof=universal_access_proof(self.proof))['value']
        self.assertEqual(server.prepared(1, handle, 'alice-token', 'durable'),
                         {'status': 'success', 'value': 'durable'}, server.diagnostics())
        committed = (self.path/'snapshot').read_bytes()
        # The real official worker writes privately, then fails consuming a
        # Nat beyond its immediate representation. It must never enter storage.
        failing = self.code.replace('S.Finish{value}',
            'S.Finish{D.VInt{0, U32.from_nat(Nat.mul(16777216n, 16777216n))}}')
        self.assertNotEqual(failing, self.code)
        self.assertEqual(server.call(failing, self.proof, 'durable', 'never-published'),
                         {'status': 'failure', 'value': None}, server.diagnostics())
        self.assertEqual((self.path/'snapshot').read_bytes(), committed)
        server.finish()
        # Seed disappearance is immaterial: recover stages only configuration.
        local = self.directory/'app'; local.mkdir()
        shutil.copyfile(self.folder/'Configuration.bend', local/'Configuration.bend')
        self.assertFalse((local/'Seed.bend').exists())
        server = self.server(folder=local)
        self.assertEqual(self.call(server), {'status': 'authentication', 'value': None})
        self.assertEqual(self.call(server, 'durable'), {'status': 'refusal', 'value': 'cancelled'})
        self.assertEqual(server.prepared(1, handle, 'durable', 'foreign'), {'status': 'failure', 'value': None})
        self.assertEqual((self.path/'snapshot').read_bytes(), committed)
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

    def test_missing_corrupt_incompatible_and_no_fallback(self):
        image = (self.path/'snapshot').read_bytes()
        (self.path/'.snapshot.tmp').write_bytes(image)
        (self.path/'snapshot.old').write_bytes(image)
        (self.path/'snapshot').unlink()
        self.assertIn(b'STORAGE', self.open_failure().stderr)
        (self.path/'snapshot').write_bytes(image[:-1])
        self.assertIn(b'STORAGE', self.open_failure().stderr)
        corrupt = bytearray(image); corrupt[64+OVERHEAD-33] ^= 1
        (self.path/'snapshot').write_bytes(corrupt)
        self.assertIn(b'checksum', self.open_failure().stderr)
        # A checksum is not a configuration/version certificate.
        incompatible = bytearray(image); incompatible[64+len(MAGIC)] ^= 1
        size = int.from_bytes(incompatible[24:32], 'big')
        incompatible[64+size-32:64+size] = hashlib.sha256(incompatible[64:64+size-32]).digest()
        incompatible[32:64] = hashlib.sha256(incompatible[:32]+incompatible[64:64+size]).digest()
        (self.path/'snapshot').write_bytes(incompatible)
        self.assertIn(b'incompatible image environment', self.open_failure().stderr)
        (self.path/'snapshot').write_bytes(image)
        # Same source, different actual executable bytes must not reopen.
        other = self.directory/'other-controller'
        other.write_bytes(BINARY.read_bytes()+b'\x00'); other.chmod(0o700)
        result = self.run_cli('--storage', self.path, '--storage-mode', 'open', binary=other)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b'incompatible image environment', result.stderr)
        changed = self.directory/'changed'; changed.mkdir()
        (changed/'Configuration.bend').write_text((self.folder/'Configuration.bend').read_text()+'\n# changed binding\n')
        result = self.run_cli('--storage', self.path, '--storage-mode', 'open', folder=changed)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b'incompatible image environment', result.stderr)
        self.assertEqual((self.path/'snapshot').read_bytes(), image)

    def test_corrupt_newest_acknowledged_slot_requires_explicit_evidence_preserving_repair(self):
        server = self.server()
        self.assertEqual(self.call(server, arguments='acknowledged-token')['status'], 'success')
        server.finish()
        image = bytearray((self.path/'snapshot').read_bytes())
        size = len(image)//2
        image[size+64+OVERHEAD] ^= 1
        (self.path/'snapshot').write_bytes(image)
        result = self.open_failure()
        self.assertIn(b'STORAGE_INVALID_SLOT', result.stderr)
        self.assertIn(b'slot 1 (B)', result.stderr)
        self.assertIn(b'checksum', result.stderr)
        self.assertEqual((self.path/'snapshot').read_bytes(), image)
        self.assertFalse(list(self.path.glob('*.evidence')))
        repaired = self.server(repair=True)
        self.assertEqual(self.call(repaired)['status'], 'refusal', repaired.diagnostics())
        self.assertEqual(self.call(repaired, 'acknowledged-token')['status'], 'authentication')
        repaired.finish()
        evidence = list(self.path.glob('snapshot.invalid-slot-1.*.evidence'))
        self.assertEqual(len(evidence), 1)
        self.assertEqual(evidence[0].read_bytes(), image[size:])
        self.assertEqual((self.path/'snapshot').read_bytes()[size:], bytes(size))

    def test_v1_snapshot_format_is_named_and_bytes_are_preserved(self):
        slot = (self.path/'snapshot').read_bytes()
        length = int.from_bytes(slot[24:32], 'big')
        old = slot[64:64+length] # the actual old single-image v1 representation
        self.assertTrue(old.startswith(MAGIC))
        (self.path/'snapshot').write_bytes(old)
        for args in ([], ['--repair-invalid-slot']):
            result = self.open_failure(*args)
            self.assertIn(b'STORAGE_FORMAT', result.stderr)
            self.assertIn(b'format v1', result.stderr)
            self.assertEqual((self.path/'snapshot').read_bytes(), old)
            self.assertFalse(list(self.path.glob('*.evidence')))

    def test_exact_descriptor_missing_modified_and_symlinked_are_rejected(self):
        descriptor = self.path/'environment'
        original = descriptor.read_bytes()
        image = (self.path/'snapshot').read_bytes()
        descriptor.unlink()
        self.assertIn(b'STORAGE', self.open_failure().stderr)
        self.assertFalse(descriptor.exists(), 'opening cannot silently create a missing binding')
        changed = bytearray(original); changed[-1] ^= 1
        descriptor.write_bytes(changed)
        self.assertIn(b'exact source or controller bytes', self.open_failure().stderr)
        self.assertEqual(descriptor.read_bytes(), changed, 'opening cannot repair a mismatched binding')
        external = self.directory/'other-environment'; external.write_bytes(original)
        descriptor.unlink(); descriptor.symlink_to(external)
        self.assertIn(b'nonregular', self.open_failure().stderr)
        descriptor.unlink(); descriptor.write_bytes(original)
        server = self.server()
        self.assertEqual(self.call(server)['status'], 'refusal', server.diagnostics())
        server.finish()
        self.assertEqual((self.path/'snapshot').read_bytes(), image)

    def test_create_open_policy_and_real_owner_contention(self):
        self.assertNotEqual(self.run_cli('--storage', self.path).returncode, 0)
        result = self.run_cli('--repair-invalid-slot')
        self.assertIn(b'--repair-invalid-slot requires --storage-mode open', result.stderr)
        result = self.run_cli('--storage', self.path, '--storage-mode', 'open', '--seed', self.directory/'absent')
        self.assertIn(b'--seed is forbidden', result.stderr)
        result = self.run_cli('--storage', self.path, '--storage-mode', 'create', '--seed', self.folder/'Seed.bend')
        self.assertNotEqual(result.returncode, 0)
        server = self.server()
        self.assertEqual(self.call(server)['status'], 'refusal')
        result = self.open_failure()
        self.assertIn(b'lock', result.stderr.lower())
        server.finish()
        # An orphan temp never wins over an acknowledged authoritative image.
        (self.path/'.snapshot.tmp').write_bytes(b'not an image')
        server = self.server()
        self.assertEqual(self.call(server)['status'], 'refusal')
        server.finish()

    def test_real_filesystem_temp_failure_leaves_ram_and_image_unchanged(self):
        server = self.server()
        self.assertEqual(self.call(server)['status'], 'refusal')
        (self.path/'.snapshot.tmp').mkdir()
        # Exceed the original 4 KiB slot so the real growth predicate selects
        # the replacement protocol (no test-only branch in production logic).
        token = 'retry-after-repair-' + 'x'*5000
        prepared = server.prepared(0, self.code, 'alice-token', proof=universal_access_proof(self.proof))
        self.assertEqual(prepared['status'], 'prepared', server.diagnostics())
        handle = prepared['value']
        self.assertEqual(server.prepared(1, handle, 'alice-token', token), {'status': 'failure', 'value': None})
        self.assertIn('STORAGE_IO', server.diagnostics())
        self.assertEqual(state_bytes(self.path), self.initial)
        self.assertEqual(self.call(server, token)['status'], 'authentication')
        (self.path/'.snapshot.tmp').rmdir()
        self.assertEqual(server.prepared(1, handle, 'alice-token', token), {'status': 'success', 'value': token})
        server.finish()

    def run_boundary(self, point, kill, expected_new, uncertain):
        path = self.directory/point
        shutil.copytree(self.base, path); self.path = path
        token = 'new-token'
        if point in ('after_write', 'after_file_sync', 'before_replace', 'after_replace', 'after_directory_sync'):
            token += 'x'*5000
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
        prepared_artifacts = set()
        if len(token) > 4096:
            prepared = server.prepared(0, self.code, 'alice-token', proof=universal_access_proof(self.proof))
            self.assertEqual(prepared['status'], 'prepared', server.diagnostics())
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
            prepared_artifacts = set(private.glob('request-*'))
            request = prepared_frame(1, prepared['value'], 'alice-token', token)
        else:
            request = frame(dict(code=self.code, proof=self.proof, credential='alice-token', arguments=token))
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
                    # Selected-call workers and staging directories are gone
                    # before storage. Retain pre-existing prepared artifacts.
                    private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
                    self.assertEqual(set(private.glob('request-*')), prepared_artifacts)
                    # Data-free pooled replacements may exist; the selected
                    # worker and per-call artifact have already been reaped.
                    idle = Path(f'/proc/{server.process.pid}/task/{server.process.pid}/children').read_text().split()
                    self.assertLessEqual(len(idle), 8)
                    os.kill(server.process.pid, signal.SIGKILL)
                    server.process.wait(timeout=10)
            finally:
                listener.close(); socket_path.unlink(missing_ok=True)
            self.assertEqual(server.process.stdout.read(), b'')
        elif uncertain:
            self.assertNotEqual(server.process.wait(timeout=180), 0, server.diagnostics())
            self.assertEqual(server.process.stdout.read(), b'')
            self.assertIn('STORAGE_UNCERTAIN', server.diagnostics())
        else:
            header = server.read(8)
            self.assertEqual(unframe(header+server.read(int.from_bytes(header, 'big'))), {'status': 'failure', 'value': None})
            self.assertIn('STORAGE_IO', server.diagnostics())
            # Safe failure allows the next frame; RAM authentication stays old.
            header = server.read(8)
            self.assertEqual(unframe(header+server.read(int.from_bytes(header, 'big'))), {'status': 'authentication', 'value': None})
            self.assertEqual(self.call(server, token)['status'], 'authentication')
            server.finish()
        if point == 'during_slot_write':
            exact = (self.path/'snapshot').read_bytes()
            result = self.open_failure()
            self.assertIn(b'STORAGE_INVALID_SLOT', result.stderr)
            self.assertIn(b'slot 1', result.stderr)
            self.assertEqual((self.path/'snapshot').read_bytes(), exact)
            self.assertFalse(list(self.path.glob('*.evidence')))
        recovered = self.server(repair=point == 'during_slot_write')
        credential = token if expected_new else 'alice-token'
        self.assertEqual(self.call(recovered, credential), {'status': 'refusal', 'value': 'cancelled'}, recovered.diagnostics())
        self.assertEqual(self.call(recovered, 'bob-token'), {'status': 'refusal', 'value': 'cancelled'})
        recovered.finish()
        if point == 'during_slot_write':
            self.assertEqual([p.read_bytes() for p in self.path.glob('*.evidence')], [exact[len(exact)//2:]])
        if not expected_new:
            self.assertEqual(state_bytes(self.path), self.initial)

    def test_recovery_peer_clearing_faults_and_process_death(self):
        for point in ('before_evidence_file_sync', 'before_evidence_directory_sync', 'after_slot_evidence_sync', 'before_slot_clear', 'during_slot_clear', 'after_slot_clear', 'after_recovery_file_sync', 'after_recovery_sync'):
            for kill in (False, True):
                with self.subTest(point=point, kill=kill):
                    self.path = self.directory/(point+str(kill))
                    shutil.copytree(self.base, self.path)
                    image = bytearray((self.path/'snapshot').read_bytes())
                    size = len(image)//2
                    peer = bytearray(image[:size])
                    length = int.from_bytes(peer[24:32], 'big')
                    payload = peer[64:64+length].replace(b'alice-token', b'ghost-token')
                    self.assertNotEqual(payload, peer[64:64+length])
                    payload[-32:] = hashlib.sha256(payload[:-32]).digest()
                    peer[16:24] = (1).to_bytes(8, 'big')
                    peer[64:64+length] = payload
                    peer[32:64] = hashlib.sha256(peer[:32]+payload).digest()
                    peer[64+OVERHEAD-32] ^= 128 # invalid future candidate
                    image[size:] = peer
                    (self.path/'snapshot').write_bytes(image)
                    self.assertIn(b'STORAGE_INVALID_SLOT', self.open_failure().stderr)
                    self.assertEqual((self.path/'snapshot').read_bytes(), image)
                    env = dict(os.environ, JAYDB_STORAGE_FAULT=point)
                    if kill:
                        gate = self.enterContext(tempfile.TemporaryDirectory(prefix='jdb-clear-', dir='/tmp'))
                        socket_path = Path(gate)/'socket'
                        listener = self.enterContext(socket.socket(socket.AF_UNIX))
                        listener.bind(str(socket_path)); listener.listen(1); listener.settimeout(180)
                        env['JAYDB_STORAGE_BARRIER'] = str(socket_path)
                    server = self.server(env=env, repair=True)
                    if kill:
                        stream, _ = listener.accept()
                        with stream:
                            self.assertEqual(stream.recv(128).decode(), point)
                            os.kill(server.process.pid, signal.SIGKILL)
                    self.assertNotEqual(server.process.wait(timeout=180), 0)
                    self.assertEqual(server.process.stdout.read(), b'')
                    if not kill: self.assertIn('STORAGE', server.diagnostics())
                    if point in ('before_evidence_file_sync', 'before_evidence_directory_sync', 'after_slot_evidence_sync', 'before_slot_clear'):
                        self.assertEqual((self.path/'snapshot').read_bytes(), image)
                    if point not in ('before_evidence_file_sync', 'before_evidence_directory_sync'):
                        self.assertIn(bytes(peer), [p.read_bytes() for p in self.path.glob('*.evidence')])
                    recovered = self.server(repair=True)
                    self.assertEqual(self.call(recovered)['status'], 'refusal', recovered.diagnostics())
                    self.assertEqual(self.call(recovered, 'ghost-token')['status'], 'authentication')
                    recovered.finish()
                    self.assertEqual((self.path/'snapshot').read_bytes()[size:], bytes(size))

    def test_process_death_at_meaningful_commit_boundaries(self):
        # SIGKILL confirms process recovery, not power-loss safety. The unit
        # fault model additionally admits old/new rename outcomes before fsync.
        for point, new in [('before_write', False), ('after_write', False),
                           ('after_file_sync', False), ('before_replace', False), ('after_replace', True),
                           ('after_directory_sync', True), ('before_publish', True), ('after_publish', True),
                           ('before_slot_write', False), ('during_slot_write', False),
                           ('after_slot_write', True), ('before_data_sync', True), ('after_data_sync', True)]:
            with self.subTest(point=point):
                self.run_boundary(point, kill=True, expected_new=new, uncertain=True)

    def test_disk_errors_and_uncertain_failure_never_emit_false_rollback(self):
        for point, new, uncertain in [('before_write', False, False),
                                       ('after_write', False, False), ('after_file_sync', False, False),
                                       ('before_replace', False, True),
                                       ('after_replace', True, True),
                                       ('after_directory_sync', True, True), ('before_publish', True, True),
                                       ('before_slot_write', False, True), ('during_slot_write', False, True),
                                       ('after_slot_write', True, True), ('before_data_sync', True, True),
                                       ('after_data_sync', True, True)]:
            with self.subTest(point=point):
                self.run_boundary(point, kill=False, expected_new=new, uncertain=uncertain)


if __name__ == '__main__':
    unittest.main(verbosity=2)
