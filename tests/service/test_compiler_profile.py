"""Real compiler/config controls; no fixture grants memory coverage."""
from pathlib import Path
import importlib.util
import hashlib
import json
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from tools.service import build_loading, build_lifecycle, build_commit, build_receiving

ROOT = Path(__file__).resolve().parents[2]


def native_builder(name):
    spec = importlib.util.spec_from_file_location('profile_' + name, ROOT / 'tools/native' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class CompilerProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='jaydb-compiler-profile-')
        cls.addClassCleanup(cls.temp.cleanup)
        cls.root = Path(cls.temp.name)
        cls.compiler = cls.root / 'bin/clang-19'
        cls.compiler.parent.mkdir()
        shutil.copyfile(Path('/usr/bin/clang-19').resolve(), cls.compiler)
        cls.compiler.chmod(0o700)
        # Preserve the real builtin headers for the copied driver. No system
        # compiler/config is edited; every fixture lives under the private root.
        resource = Path(subprocess.check_output(['/usr/bin/clang-19', '--print-resource-dir'], text=True).strip())
        target = cls.root / 'lib/clang' / resource.name
        target.parent.mkdir(parents=True)
        target.symlink_to(resource, target_is_directory=True)
        header = cls.root / 'automatic-config.h'
        header.write_text('#error JAYDB_automatic_configuration_fixture_was_loaded\n')
        (cls.compiler.parent / 'x86_64-pc-linux-gnu-clang.cfg').write_text('-include ' + str(header) + '\n')
        control = subprocess.run([str(cls.compiler), '-fsyntax-only', '-x', 'c', '/dev/null'],
                                 capture_output=True, text=True)
        if control.returncode == 0 or 'JAYDB_automatic_configuration_fixture_was_loaded' not in control.stderr:
            raise AssertionError(('The causal default-config control did not run', control.stderr))
        selected = subprocess.run([str(cls.compiler), '--no-default-config', '-fsyntax-only',
                                   '-x', 'c', '/dev/null'], capture_output=True, text=True)
        if selected.returncode:
            raise AssertionError(selected.stderr)

    def test_service_shims_compile_with_private_default_config_ignored(self):
        for name, builder in (('loading', build_loading), ('lifecycle', build_lifecycle),
                              ('commit', build_commit), ('receiving', build_receiving)):
            with self.subTest(builder=name), patch.object(builder, 'COMPILER', self.compiler):
                output = self.root / (name + '.so')
                report = builder.build(output)
                self.assertTrue(output.is_file())
                self.assertEqual(json.loads(output.with_suffix('.so.json').read_text()), report)
                if name in ('loading', 'lifecycle'):
                    self.assertIn('--no-default-config', report['arguments'])
                else:
                    self.assertFalse(report['compilerDefaultConfiguration'])
                    self.assertTrue(report.get('criticalIsLeaf', report.get('auditedProductionPrefixIsLeaf')))

    def test_field_constructor_and_both_recipe_link_modes_ignore_default_config(self):
        for name, kwargs in (('build_field', {}), ('build_constructor', {}),
                             ('build_recipe', {}), ('build_recipe', {'object_only': True})):
            builder = native_builder(name)
            with self.subTest(builder=name, kwargs=kwargs), patch.object(builder, 'CLANG', self.compiler):
                output = self.root / (name + ('.o' if kwargs else '.so'))
                report = builder.build(output, **kwargs)
                self.assertTrue(output.is_file())
                self.assertFalse(report['compilerDefaultConfiguration'])
                self.assertTrue(report['criticalIsLeaf'])

    def test_checked_codec_c_build_ignores_config_without_changing_emitted_source(self):
        # Historical emitted C is a frozen test input; this test validates the
        # builder, not its general semantic correspondence or memory coverage.
        source = ROOT / 'tests/native/evidence/accounted-codec.c'
        original = source.read_bytes()
        builder = native_builder('build')
        output = self.root / 'checked-codec.so'
        with patch.object(builder, 'CLANG', str(self.compiler)):
            report = builder.build_module(source, output, enter_cid='CID_Native_enter',
                                          timeout_ns=120 * 10**9)
        self.assertEqual(source.read_bytes(), original)
        self.assertFalse(report['compilerDefaultConfiguration'])
        self.assertEqual(report['compilerDriverFlags'], ['--no-default-config'])
        self.assertEqual(report['compilerSha256'], hashlib.sha256(self.compiler.read_bytes()).hexdigest())
        self.assertFalse(report['accountedCoverageGrantedByJson'])
        self.assertFalse(report['accountedRecipeAudit']['compilerDefaultConfiguration'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
