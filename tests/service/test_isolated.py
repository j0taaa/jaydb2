"""Explicit startup selection; synthetic scripts are marked as fixtures."""
from pathlib import Path
import json
import os
import subprocess
import tempfile
import unittest

from tools.service.isolated import BOOTSTRAP, ENTRIES, PYTHON, command


ROOT = Path(__file__).resolve().parents[2]


class IsolatedEntryTests(unittest.TestCase):
    def test_fixed_entrypoints_and_original_arguments(self):
        arguments = ['--', 'node', '/tmp/a b/x.mjs']
        result = command(ROOT, 'admission', arguments)
        self.assertEqual(result[:6], [PYTHON, '-I', '-S', '-B', '-c', BOOTSTRAP])
        self.assertEqual(result[6:8], [str(ROOT), 'tools/admission/run.py'])
        self.assertEqual(result[8:], arguments)
        self.assertTrue(Path(result[0]).is_absolute())

    def test_arbitrary_entrypoint_is_not_accepted(self):
        for entry in ('../Client.py', 'Client.py', 'os', 'service/../../Client.py'):
            with self.subTest(entry=entry), self.assertRaises(ValueError):
                command(ROOT, entry)

    def test_fixture_bootstrap_preserves_arguments_pid_environment_and_cwd(self):
        with tempfile.TemporaryDirectory(prefix='jaydb2-isolated-') as tmp:
            capsule = Path(tmp) / "capsule with 'quote"
            target = capsule / ENTRIES['native_simple']
            target.parent.mkdir(parents=True)
            target.write_text(
                'import json,os,sys\n'
                'print(json.dumps({"argv":sys.argv,"pid":os.getpid(),'
                '"cwd":os.getcwd(),"home":os.environ["HOME"],'
                '"sentinel":os.environ["JAYDB_STARTUP_TEST"],'
                '"site":"site" in sys.modules,"isolated":sys.flags.isolated,'
                '"no_site":sys.flags.no_site,"ignore_env":sys.flags.ignore_environment,'
                '"safe_path":sys.flags.safe_path,"no_pyc":sys.flags.dont_write_bytecode}))\n')
            arguments = ['one two', "'quoted'", '$(literal)', '\nline', '--not-python-code']
            env = {**os.environ, 'HOME': str(Path(tmp) / 'home'),
                   'JAYDB_STARTUP_TEST': 'retained exactly'}
            process = subprocess.Popen(command(capsule, 'native_simple', arguments), cwd=tmp,
                                       env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            out, err = process.communicate(timeout=10)
            self.assertEqual((process.returncode, err), (0, b''))
            result = json.loads(out)
            self.assertEqual(result['argv'], [str(target), *arguments])
            self.assertEqual(result['pid'], process.pid)
            self.assertEqual(result['cwd'], tmp)
            self.assertEqual(result['home'], env['HOME'])
            self.assertEqual(result['sentinel'], env['JAYDB_STARTUP_TEST'])
            self.assertFalse(result['site'])
            for flag in ('isolated', 'no_site', 'ignore_env', 'safe_path', 'no_pyc'):
                self.assertTrue(result[flag])

    def test_actual_entries_skip_user_pth_and_environment_sitecustomize(self):
        # This hook is a fixture in a private HOME, not customer source.
        with tempfile.TemporaryDirectory(prefix='jaydb2-startup-hooks-') as tmp:
            base = Path(tmp)
            marker = base / 'startup-marker'
            site = base / 'home/.local/lib/python3.12/site-packages'
            site.mkdir(parents=True)
            injected = base / 'python-path'
            injected.mkdir()
            code = f'from pathlib import Path\nPath({str(marker)!r}).open("a").write("hook\\n")\n'
            (site / 'jaydb_startup_hook.py').write_text(code)
            (site / 'jaydb-startup.pth').write_text('import jaydb_startup_hook\n')
            (injected / 'sitecustomize.py').write_text(code)
            env = {**os.environ, 'HOME': str(base / 'home'), 'PYTHONPATH': str(injected)}
            for entry, args in (('service', ['--help']), ('native_simple', ['--help']),
                                ('admission', ['--describe'])):
                with self.subTest(entry=entry):
                    marker.unlink(missing_ok=True)
                    control = subprocess.run([PYTHON, '-B', str(ROOT / ENTRIES[entry]), *args],
                                             env=env, capture_output=True, timeout=10)
                    self.assertEqual(control.returncode, 0, control.stderr)
                    self.assertTrue(marker.exists())
                    self.assertGreaterEqual(len(marker.read_text().splitlines()), 2)
                    marker.unlink()
                    selected = subprocess.run(command(ROOT, entry, args), env=env,
                                              capture_output=True, timeout=10)
                    self.assertEqual(selected.returncode, 0, selected.stderr)
                    self.assertFalse(marker.exists())
                    self.assertEqual(selected.stdout, control.stdout)


if __name__ == '__main__':
    unittest.main()
