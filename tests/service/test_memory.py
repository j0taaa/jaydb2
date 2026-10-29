"""Window-reader fixtures and a real INCOMPLETE refusal; no coverage theorem."""
from dataclasses import replace
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from tools.accounting.client import Snapshot,WindowSnapshot,FROZEN,INCOMPLETE,IncompleteCoverage
from tools.service.memory import MemoryWindow,MemoryExcess,InvalidMemoryObservation


def numeric_fixture(*,current=40,peak=100,flags=FROZEN):
    # Explicit numerical fixture. It is not an actual allocation observation.
    snapshot=Snapshot(20,current,1000,200,30,3,FROZEN,flags)
    return WindowSnapshot(snapshot,1,1,10,100,0,0,peak,170,17,flags)


class MemoryWindows(unittest.TestCase):
    def monitor(self,window,ceiling=100):
        return MemoryWindow(SimpleNamespace(window_read=lambda:window),1,ceiling)

    def test_equal_local_peak_fits_despite_larger_global_peak(self):
        window=numeric_fixture()
        self.assertIs(self.monitor(window).poll(),window)
        self.assertIs(self.monitor(window,10**5000).poll(),window)

    def test_local_transient_excess_keeps_original_scope_sequence_and_time(self):
        window=numeric_fixture(peak=101)
        with self.assertRaises(MemoryExcess) as failure:
            self.monitor(window).poll()
        error=failure.exception
        self.assertEqual(error.measured,101)
        self.assertEqual((error.witness.scope_id,error.witness.sequence,error.witness.monotonic_ns),(1,17,170))
        self.assertEqual(error.witness.flags,FROZEN)
        self.assertIs(error.window,window)

    def test_incomplete_above_ceiling_does_not_become_public_excess(self):
        with self.assertRaises(IncompleteCoverage):
            self.monitor(numeric_fixture(peak=10000,flags=FROZEN|INCOMPLETE),1).poll()

    def test_previous_scope_or_closed_scope_cannot_monitor_next_helper(self):
        with self.assertRaises(ValueError):
            self.monitor(replace(numeric_fixture(),scope_id=2)).poll()
        with self.assertRaises(InvalidMemoryObservation):
            self.monitor(replace(numeric_fixture(),state=2,end_sequence=20,end_monotonic_ns=200)).poll()

    def test_inconsistent_provenance_never_justifies_excess(self):
        window=numeric_fixture(peak=101)
        for changed in (replace(window,peak_sequence=9),replace(window,peak_sequence=21),
                        replace(window,peak_monotonic_ns=99),replace(window,peak_monotonic_ns=201),
                        replace(window,peak=39),replace(window,peak_flags=0)):
            with self.subTest(changed=changed):
                with self.assertRaises(InvalidMemoryObservation):
                    self.monitor(changed,1).poll()

    def test_exception_constructor_requires_strict_real_window_excess(self):
        with self.assertRaises(ValueError):
            MemoryExcess(numeric_fixture(),100,1)
        with self.assertRaises(IncompleteCoverage):
            MemoryExcess(numeric_fixture(flags=3),1,1)

    def test_real_counter_incomplete_stops_and_reaps_helper(self):
        from tools.accounting.build import build
        from tools.service.build_loading import build as build_loading
        from tools.service.build_lifecycle import build as build_lifecycle
        with tempfile.TemporaryDirectory(prefix='jaydb2-window-memory-') as tmp:
            directory=Path(tmp)
            library,tracer=build(directory/'accounting')
            build_loading(directory/'loading.so')
            build_lifecycle(directory/'lifecycle.so')
            code='''import sys,os,time,json,subprocess
sys.path.insert(0,sys.argv[1])
from tools.accounting.client import Library,Counter,IncompleteCoverage
from tools.service.memory import MemoryWindow
from tools.service.controller import helper
from tools.service.loading import Runtime
from tools.service.lifecycle import LifecycleRuntime
import resource
resource.setrlimit(resource.RLIMIT_CORE,(0,resource.getrlimit(resource.RLIMIT_CORE)[1]))
runtime=LifecycleRuntime.load(sys.argv[4],loading_runtime=Runtime.load(sys.argv[3]))
lib=Library(sys.argv[2]);counter=Counter(lib,fd=int(os.environ['JAYDB_ACCOUNTING_FD']))
scope=lib.window_begin();window=MemoryWindow(counter,scope.scope_id,1)
try:
  helper([sys.executable,'-c','import time;time.sleep(60)'],time.monotonic_ns()+10**10,1,memory_window=window)
  raise AssertionError('Incomplete observation was used')
except IncompleteCoverage:
  pass
assert lib.window_barrier().require_scope(scope.scope_id).active
lib.window_end();counter.close()
print(json.dumps({'refusedIncomplete':True,'windowPreserved':True}))
'''
            probe=directory/'probe.py';probe.write_text(code)
            result=subprocess.run([str(tracer),'--',sys.executable,'-B',str(probe),str(ROOT),str(library),
                str(directory/'loading.so'),str(directory/'lifecycle.so')],
                capture_output=True,text=True,timeout=30)
            self.assertEqual(result.returncode,0,result.stderr+result.stdout)
            self.assertEqual(json.loads(result.stdout),{'refusedIncomplete':True,'windowPreserved':True})


if __name__=='__main__':
    unittest.main(verbosity=2)
