"""Task client/workspace checks that need no Bend distribution or native build."""
from pathlib import Path
from io import BytesIO
from types import SimpleNamespace
import tempfile
import unittest
from unittest.mock import patch, MagicMock

from applications.tasks.app import ROOT, Database, database, prepare, task_command, workspace_directory


class TaskAccessoryTests(unittest.TestCase):
    def test_create_freezes_sources_and_open_never_repackages_or_requires_seed(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp) / 'list'
            directory = workspace_directory(workspace, 'create')
            original = {p.name: p.read_bytes() for p in directory.iterdir()}
            self.assertIn('Seed.bend', original)
            (directory / 'Seed.bend').unlink()
            with patch('applications.tasks.app.prepare', side_effect=AssertionError('open recopied sources')):
                self.assertEqual(workspace_directory(workspace, 'open'), directory)
            self.assertEqual({p.name: p.read_bytes() for p in directory.iterdir()},
                             {k: v for k, v in original.items() if k != 'Seed.bend'})
            with self.assertRaises(FileExistsError):
                workspace_directory(workspace, 'create')
            self.assertEqual((directory/'Client.bend').read_bytes(), original['Client.bend'])

    def test_open_missing_workspace_leaves_no_files(self):
        with tempfile.TemporaryDirectory() as tmp:
            missing = Path(tmp) / 'missing'
            with self.assertRaisesRegex(ValueError, 'Missing task workspace'):
                workspace_directory(missing, 'open')
            self.assertFalse(missing.exists())

    def test_open_spawn_has_no_seed_and_uses_existing_package(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp) / 'list'
            directory = workspace_directory(workspace, 'create')
            (directory/'Seed.bend').unlink()
            process = MagicMock()
            process.__enter__.return_value = process
            process.__exit__.return_value = False
            process.returncode = 0
            with patch('applications.tasks.app.subprocess.Popen', return_value=process) as start:
                with database(workspace=workspace, storage_mode='open', threads=1) as db:
                    self.assertEqual(db.code, (directory/'Client.bend').read_text())
            command = start.call_args.args[0]
            self.assertNotIn('--seed', command)
            self.assertEqual(command[command.index('--storage-mode')+1], 'open')
            self.assertEqual(command[command.index('--storage')+1], str(workspace/'db'))

    def test_prepare_retains_existing_call_signature_and_exact_programs(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            prepare(directory, root=ROOT)
            for name in ['Client.bend', 'ClientProof.bend', 'Configuration.bend', 'Seed.bend']:
                self.assertEqual((directory/name).read_bytes(), (ROOT/'applications/tasks'/name).read_bytes())

    def test_commands_keep_boolean_types_and_reject_bad_arity(self):
        self.assertEqual(task_command(['save','t1','Buy bread']), ['save','t1','Buy bread',False])
        self.assertEqual(task_command(['cancel','t1','No write','true']), ['cancel','t1','No write',True])
        self.assertEqual(task_command(['list']), ['list'])
        for args in [[], ['list','extra'], ['save','t1'], ['save','t1','Title','yes'], ['view']]:
            with self.subTest(args=args), self.assertRaises(ValueError):
                task_command(args)

    def test_workspace_options_must_be_paired_before_launch(self):
        with patch('applications.tasks.app.subprocess.Popen', side_effect=AssertionError('launched')):
            for kwargs in [{'workspace':'unused'}, {'storage_mode':'open'}]:
                with self.assertRaisesRegex(ValueError, 'together'):
                    with database(**kwargs):
                        self.fail('unreachable')

    def test_incomplete_response_is_unknown_outcome_without_retry(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            prepare(directory)
            for output in [b'', b'\0'*7, (20).to_bytes(8,'big')+b'\0']:
                with self.subTest(output=output):
                    process = SimpleNamespace(stdin=BytesIO(), stdout=BytesIO(output))
                    client = Database(process, directory)
                    with self.assertRaisesRegex(RuntimeError, 'outcome may be unknown'):
                        client.call('alice-token', ['save','t1','Title',False])
                    self.assertTrue(process.stdin.getvalue(), 'one request was submitted before transport loss')


if __name__ == '__main__':
    unittest.main()
