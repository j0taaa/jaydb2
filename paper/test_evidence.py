"""Checks on the fresh evidence and controls for plausible data corruption."""
import copy
import importlib.util
from pathlib import Path
import re
import tempfile
import unittest

spec=importlib.util.spec_from_file_location('paper_evidence',Path(__file__).with_name('evidence.py'))
evidence=importlib.util.module_from_spec(spec);spec.loader.exec_module(evidence)


class EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.data=evidence.load()

    def corrupt(self,edit,message):
        data=copy.deepcopy(self.data);edit(data)
        with self.assertRaisesRegex(ValueError,message):evidence.validate(data)

    def test_fresh_inputs_and_rendered_macros(self):
        previous=evidence.OUT
        try:
            with tempfile.TemporaryDirectory() as folder:
                evidence.OUT=Path(folder)
                macros=evidence.derive(self.data)
                self.assertIn('OrdinaryMedianSeconds',macros)
                self.assertIn('PreparedMedianMs',macros)
                self.assertIn('BreakEvenCalls',macros)
                self.assertTrue(all(re.fullmatch('[A-Z][a-zA-Z]*',name) for name in macros))
                self.assertTrue((Path(folder)/'scaling-coordinates.tex').is_file())
                readme=(evidence.ROOT/'paper/README.md').read_text()
                for name in macros:self.assertIn('`\\'+name+'`',readme)
        finally:evidence.OUT=previous

    def test_duplicate_iteration(self):
        self.corrupt(lambda d:d['ordinary']['records'][0]['samples'][1].update(iteration=1),'samples')

    def test_wrong_result_even_with_checked_flag(self):
        self.corrupt(lambda d:d['ordinary']['records'][0]['samples'][0].update(actual={'status':'success','value':999}),'incorrect output')

    def test_boolean_is_not_integer(self):
        self.corrupt(lambda d:d['ordinary']['records'][0]['samples'][0].update(actual={'status':'success','value':False}),'incorrect output')

    def test_missing_metadata(self):
        self.corrupt(lambda d:d['prepared']['metadata'].pop('commit'),'Missing metadata')

    def test_missing_prepared_mode(self):
        self.corrupt(lambda d:d['prepared']['records'].pop(),'Prepared program/mode')

    def test_policy_is_actually_checked(self):
        self.corrupt(lambda d:d['comparison']['policy_checks'].pop(),'policy refusal')

    def test_superuser_does_not_establish_rls(self):
        self.corrupt(lambda d:d['comparison']['settings']['postgresql']['role'].__setitem__(1,True),'durability/RLS')

    def test_durable_settings(self):
        self.corrupt(lambda d:d['comparison']['settings']['sqlite'].update(synchronous=1),'SQLite durability')

    def test_missing_update_readback(self):
        def edit(d):
            row=next(s for r in d['comparison']['records'] if r['engine']=='jaydb2' for s in r['samples'] if s['workload']=='update')
            row.pop('stored_value_checked')
        self.corrupt(edit,'stored update')

    def test_missing_scaling_mode(self):
        self.corrupt(lambda d:d['scaling']['records'].pop(),'scaling population/mode')

    def test_failed_gate_is_not_valid_paper_evidence(self):
        self.corrupt(lambda d:d['verification']['commands'][0].update(returncode=1),'verification gate failed')

    def test_summary_uses_inclusive_quartiles(self):
        result=evidence.summary([dict(elapsed_ns=x) for x in (1,2,3,4,100)])
        self.assertEqual((result['median'],result['qone'],result['qthree']),(3,2,4))

if __name__=='__main__':unittest.main(verbosity=2)
