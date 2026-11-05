"""Mutating the executed publication function must break its linked proof."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest
from tools.bend import ROOT, executable, environment

class NegativeProofTests(unittest.TestCase):
    def test_actual_publication_mutation_fails(self):
        with tempfile.TemporaryDirectory(dir=ROOT/'target/bend-host',prefix='negative-') as tmp:
            local=Path(tmp)
            for name in ('contract','src','proof'):(local/name).symlink_to(ROOT/name,target_is_directory=True)
            shutil.copytree(ROOT/'host',local/'host')
            policy=local/'host/Policy.bend'
            source=policy.read_text();old='Publication{old, response}'
            self.assertIn(old,source)
            policy.write_text(source.replace(old,'Publication{response, response}'))
            result=subprocess.run([str(executable()),str(local/'host/VERIFY.bend'),'--check-only'],
                env=environment(),capture_output=True,text=True,timeout=120)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('SOME PROOFS FAIL',result.stdout+result.stderr)
            self.assertIn('no_proposal_state_preserves_state',result.stdout+result.stderr)
