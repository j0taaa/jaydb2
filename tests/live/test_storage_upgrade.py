"""Run with JAYDB_LEGACY_BINARY pointing to a built complete-image controller."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from applications.tasks.app import prepare
from tests.service.test_end_to_end import ROOT, Server


@unittest.skipUnless(os.environ.get('JAYDB_LEGACY_BINARY'), 'requires a built main worktree')
class StorageUpgradeTest(unittest.TestCase):
    def test_legacy_tasks_upgrade_and_rejections(self):
        legacy = Path(os.environ['JAYDB_LEGACY_BINARY']).resolve()
        with tempfile.TemporaryDirectory(prefix='jaydb-upgrade-test-') as scratch:
            directory = Path(scratch)
            app = directory / 'app'
            app.mkdir()
            prepare(app)
            config = app / 'Configuration.bend'
            code = (app / 'Client.bend').read_text()
            proof = (app / 'ClientProof.bend').read_text().replace(
                'def B.certificate(s, valid, identity, n):\n'
                '  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)',
                'def B.certificate(ctx, args, s, valid, identity, n):\n'
                '  certify(ctx, args, B.code(), s, valid, identity, n)',
            )
            old = directory / 'old'
            new = directory / 'new'

            def service(path, mode, binary=None):
                return Server(app, binary=binary, threads=1, seed=mode == 'create',
                              arguments=['--storage', str(path), '--storage-mode', mode])

            def upgrade(source, destination, configuration=config, executable=legacy):
                return subprocess.run(
                    [ROOT / 'jaydb2', '--configuration', configuration, '--threads', '1',
                     '--storage', destination, '--upgrade-from', source, '--legacy-jaydb2', executable],
                    input=b'', capture_output=True, cwd=ROOT, timeout=180,
                )

            def register(server):
                response = server.prepared(0, code, 'alice-token', proof=proof)
                self.assertEqual(response['status'], 'prepared', server.diagnostics())
                return response['value']

            def call(server, handle, user, args, expected):
                self.assertEqual(server.prepared(1, handle, user + '-token', args),
                                 {'status': 'success', 'value': expected}, server.diagnostics())

            rows = [('alice', 'a1', 'Buy bread', False), ('alice', 'a2', 'Call Zoë', True),
                    ('bob', 'b1', 'Review report', False)]
            original = service(old, 'create', legacy)
            try:
                handle = register(original)
                for user, key, title, completed in rows:
                    call(original, handle, user, ['save', key, title, completed], key)
                result = upgrade(old, new)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(b'cannot lock legacy storage', result.stderr)
                self.assertFalse(new.exists())
                original.finish()
            finally:
                original.close()

            before = {path.name: path.read_bytes() for path in old.iterdir()}
            result = upgrade(old, new)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout, b'')
            self.assertEqual({path.name: path.read_bytes() for path in old.iterdir()}, before)

            checkpoint = (new / 'checkpoint-0').read_bytes()
            header = len(b'jaydb2-wal-checkpoint-v1\n')
            descriptor_size = int.from_bytes(checkpoint[header + 8:header + 16], 'big')
            state_offset = len(b'jaydb2-image-v1\n') + 64 + 4 * 8
            self.assertEqual(checkpoint[header + 16 + descriptor_size:-4],
                             before['snapshot'][state_offset:-32])

            recovered = service(new, 'open')
            try:
                handle = register(recovered)
                for user, key, title, completed in rows:
                    call(recovered, handle, user, ['view', key],
                         dict(id=key, owner=user, title=title, completed=completed))
                recovered.finish()
            finally:
                recovered.close()

            occupied = directory / 'empty'
            occupied.mkdir()
            result = upgrade(old, occupied)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'new directory', result.stderr)
            self.assertEqual(list(occupied.iterdir()), [])

            rejected = directory / 'rejected'
            result = upgrade(old, rejected, executable='/usr/bin/true')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'original controller executable', result.stderr)
            self.assertFalse(rejected.exists())

            changed = app / 'Changed.bend'
            changed.write_text(config.read_text() + '\n# Different exact environment.\n')
            result = upgrade(old, rejected, configuration=changed)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'incompatible image environment', result.stderr)
            self.assertFalse(rejected.exists())

            corrupt = directory / 'corrupt'
            shutil.copytree(old, corrupt)
            image = bytearray(before['snapshot'])
            image[state_offset] ^= 1
            (corrupt / 'snapshot').write_bytes(image)
            result = upgrade(corrupt, rejected)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'image checksum mismatch', result.stderr)
            self.assertFalse(rejected.exists())
            self.assertEqual((corrupt / 'snapshot').read_bytes(), image)
