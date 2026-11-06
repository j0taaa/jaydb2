"""Cheap packaging tests; native/proof checks are the separate check.py command."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('starter_create', HERE / 'create.py')
starter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(starter)


class StarterTests(unittest.TestCase):
    def test_both_profiles_export_matching_concrete_and_universal_wrappers(self):
        with tempfile.TemporaryDirectory() as temporary:
            for profile in ('crud', 'conditional'):
                directory = starter.create(Path(temporary) / profile, profile)
                original = (directory / 'ClientProof.bend').read_text()
                prepared = (directory / 'PreparedProof.bend').read_text()
                self.assertIn(starter.CONCRETE, original)
                self.assertEqual(prepared, starter.universal_proof(original))
                expected = 'case ListTasks{}' if profile == 'crud' else 'M.compare_exchange'
                self.assertIn(expected, (directory / 'Client.bend').read_text())
                for name in ('Configuration', 'Policy', 'Proofs', 'Ownership', 'Seed', 'Orders', 'Foundations', 'Laws', 'Query', 'Action'):
                    self.assertTrue((directory / (name + '.bend')).is_file(), name)
                if profile == 'conditional':
                    for name in ('Task', 'Mutation', 'ReadProgram', 'ReadOnly', 'Value', 'Int64'):
                        self.assertTrue((directory / (name + '.bend')).is_file(), name)

    def test_existing_directory_and_symlink_are_not_modified(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            directory = root / 'existing'; directory.mkdir()
            marker = directory / 'keep'; marker.write_text('original')
            link = root / 'link'; link.symlink_to(directory, target_is_directory=True)
            for path in (directory, link):
                with self.assertRaises(FileExistsError):
                    starter.create(path)
            self.assertEqual(marker.read_text(), 'original')
            self.assertEqual(list(directory.iterdir()), [marker])

    def test_changed_certificate_wrapper_requires_explicit_update(self):
        with self.assertRaises(ValueError):
            starter.universal_proof('def B.certificate(): Unit{}')


if __name__ == '__main__':
    unittest.main()
