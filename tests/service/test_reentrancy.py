"""Real ABI6 output remains owned during reentrant shutdown from a signal.

The echo is a primary-checked native fixture, not a production certificate.
Each signal probe runs in its own process so a regression cannot crash unittest.
"""
from pathlib import Path
import inspect
import json
import re
import signal
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.native.build_simple import build_module
from tools.service.abi_simple import SimpleModule, NativeOwnershipPending
from tools.service.controller import IncompleteIntegration, RequestProposal
from tools.service.entry import prepare_entry
from tests.service.observation import fixture_loading
from tests.service.test_simple_service import HostFixture


def probe(mode, binary):
    prepare_entry()
    fixture_loading()
    module = SimpleModule(binary)
    database = HostFixture()
    database.lifecycle_runtime = module._lifecycle_runtime
    database.modules['echo'] = module
    observed = []
    reached = False
    body = SimpleModule._run_owned
    lines, start = inspect.getsourcelines(body)
    boundary = start + next(i for i, line in enumerate(lines) if 'if status != result.status' in line)

    def handler(*_):
        leases = len(database.lifecycle_runtime.live_leases)
        try:
            if mode == 'database':
                database.close()
            elif mode == 'module':
                module.close()
            else:
                module.run(b'nested', capacity=100)
        except (IncompleteIntegration, NativeOwnershipPending):
            observed.append((leases, len(database.lifecycle_runtime.live_leases),
                             module.library is not None, not database._closed))
        else:
            raise AssertionError('Reentrant operation consumed an active output')

    def trace(frame, event, argument):
        nonlocal reached
        if event == 'line' and frame.f_code is body.__code__ and frame.f_lineno == boundary and not reached:
            reached = True
            signal.raise_signal(signal.SIGUSR1)
        return trace

    previous = signal.signal(signal.SIGUSR1, handler)
    database.handler = lambda _: RequestProposal(module.run(b'actual-output', capacity=100))
    try:
        sys.settrace(trace)
        result = database.request(b'request')
        sys.settrace(None)
        assert result == b'actual-output'
        assert observed == [(1, 1, True, True)], observed
        assert not database.lifecycle_runtime.live_leases
        assert module.run(b'next', capacity=100) == b'next'
        database.close()
        assert module.library is None
        print(json.dumps(dict(mode=mode,guarded=True,exactOutput=True,reusable=True,leases=0)))
    finally:
        sys.settrace(None)
        signal.signal(signal.SIGUSR1, previous)
        database.close()


class ReentrantOutputTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix='jaydb-reentrancy-')
        cls.addClassCleanup(cls.directory.cleanup)
        folder = Path(cls.directory.name)
        source = folder/'echo.bend'
        source.write_text((ROOT/'tests/native/fixtures/echo.bend').read_text().replace(
            '../../../native/effects.bend', str(ROOT/'native/effects.bend')))
        emitted = folder/'echo.c'
        subprocess.run(['node', str(ROOT/'tests/native/emit_fixture.mjs'),
            str(ROOT/'.tools/bend-source-2.0.39/bend2'), str(source), str(emitted), 'generic'],
            check=True, capture_output=True, text=True)
        cls.binary = folder/'echo.so'
        text = emitted.read_text()
        cids = {name: re.findall(r'^#define (CID_\w*_'+name+r') \d+$', text, re.M)
                for name in ('read', 'write')}
        if any(len(found) != 1 for found in cids.values()):
            raise AssertionError('Echo fixture must have one read/write binding')
        build_module(emitted, cls.binary, input_cid=cids['read'][0], output_cid=cids['write'][0])

    def check(self, mode):
        result = subprocess.run([sys.executable, '-B', __file__, '--probe', mode, str(self.binary)],
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout+result.stderr)
        self.assertTrue(json.loads(result.stdout)['guarded'])

    def test_signal_cannot_close_database_before_output_copy(self):
        self.check('database')

    def test_signal_cannot_close_module_before_output_copy(self):
        self.check('module')

    def test_signal_cannot_replace_the_active_output_by_reentering_run(self):
        self.check('run')


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--probe':
        probe(sys.argv[2], sys.argv[3])
    else:
        unittest.main(verbosity=2)
