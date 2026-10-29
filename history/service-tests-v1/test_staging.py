"""Read-only public environment and complete materialization of its tooling."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from tools.service.staging import Environment


class StagingTests(unittest.TestCase):
    def test_registered_closure_has_no_python_recursion_depth_limit(self):
        example=ROOT/'examples/sem-observacoes'
        with tempfile.TemporaryDirectory() as tmp:
            tmp=Path(tmp)
            config=(example/'Configuration.bend').read_bytes()
            (tmp/'Configuration.bend').write_bytes(b'import ./Lib0.bend as Registered\n'+config)
            (tmp/'Seed.bend').write_bytes((example/'Seed.bend').read_bytes())
            count=1250
            for i in range(count):
                header=f'import ./Lib{i+1}.bend as Next\n' if i+1<count else 'import Base\n'
                (tmp/f'Lib{i}.bend').write_text(header+'def value() -> Nat:\n  0n\n')
            recursion_limit=sys.getrecursionlimit()
            environment=Environment(tmp/'Configuration.bend',tmp/'Seed.bend')
            self.assertEqual(sum(name.startswith('Lib') for name in environment.sources),count)
            self.assertEqual(sys.getrecursionlimit(),recursion_limit)

    def test_environment_tables_are_immutable_and_nested_tooling_is_retained(self):
        example=ROOT/'examples/sem-observacoes'
        environment=Environment(example/'Configuration.bend',example/'Seed.bend')
        for table in (environment.sources,environment.seed_sources,environment.tooling):
            key=next(iter(table))
            with self.assertRaises(TypeError):
                table[key]=b'changed after initialization'
        for name in ('tools/service/commit.S','native/accounting/deadline.h',
                     'tools/accounting/client.py','tools/admission/safe-templates.mjs'):
            self.assertEqual(environment.tooling[name],(ROOT/name).read_bytes())
        self.assertNotIn('Seed.bend',environment.sources)
        self.assertNotIn('tools/accounting/CLOSURE.json',environment.tooling)
        with tempfile.TemporaryDirectory() as tmp:
            runtime=environment.materialize_tooling(Path(tmp)/'runtime')
            for name in ('tools/service/commit.S','native/accounting/deadline.h'):
                self.assertEqual((runtime/name).read_bytes(),environment.tooling[name])
            stage=Path(tmp)/'decode';stage.mkdir()
            environment.stage(stage,'decode')
            self.assertEqual((stage/'Environment.bend').read_bytes(),environment.sources['Environment.bend'])


if __name__=='__main__':
    unittest.main()
