"""Exact integer simulation through ordinary certified database requests."""
import json
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_gpu import StateFeed

APP = ROOT/'applications/simulation'
CODE, PROOF = ((APP/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
CONCRETE = PROOF.replace('def B.certificate(ctx, args, s, valid, identity, n):\n  +ctx = ctx\n  +args = args',
    'def B.certificate(s, valid, identity, n):\n  +ctx = I.context()\n  +args = I.arguments()')
PARAMETERS = {'alice': (123456789, 0, 250), 'bob': (3735928559, 3, 700)}
MASK = 0xffffffff


def oracle(depth, steps, user='alice', vector=False):
    seed, drift, vol = PARAMETERS[user]
    if vector:
        import numpy as np
        rng = (np.arange(1 << depth, dtype=np.uint64)*747796405+seed) & MASK
        values = np.full(1 << depth, 1000000, dtype=np.uint64)
        for _ in range(steps):
            rng = (rng*1664525+1013904223) & MASK
            values = (values+drift+((rng >> 16) % (2*vol+1))+2**32-vol) & MASK
        return dict(sum=int(values.sum()) & MASK, max=int(values.max()),
                    above=int((values > 1000000).sum()), paths=1 << depth)
    values = []
    for index in range(1 << depth):
        rng, value = (seed+index*747796405) & MASK, 1000000
        for _ in range(steps):
            rng = (rng*1664525+1013904223) & MASK
            value = (value+drift+((rng >> 16) % (2*vol+1))-vol) & MASK
        values.append(value)
    return dict(sum=sum(values) & MASK, max=max(values), above=sum(v > 1000000 for v in values), paths=len(values))


def state(results):
    return dict(tables=[dict(name='results', rows=[dict(id=u, **results[u]) for u in sorted(results)]),
        dict(name='scenarios', rows=[dict(id=u, seed=p[0], drift=p[1], volatility=p[2]) for u, p in PARAMETERS.items()])],
        users=[dict(credential=u+'-token', id=u, kind='user') for u in PARAMETERS])


def artifact(server, gpu):
    private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
    native, = private.glob('request-*/*.program')
    from paper.bench.gpu_programs import validate
    report = validate(native, gpu)
    report['emitted_bangs'] = int(re.search(rb'^#define\s+BANGS\s+(\d+)',
        (native.parent/'checked.c').read_bytes(), re.M)[1])
    assert report['emitted_bangs'] > 0
    return native, report


def publications(feed):
    published, current = [], None
    for snapshot, event in zip(feed.states, feed.events):
        if event['event'] in ('initialized', 'completed'):
            published.append(snapshot)
            current = snapshot
        else:
            assert snapshot == current, 'metadata event changed published state'
    return published


def exercise(threads, gpu=False, env=None, trace=None, ordinary=False):
    with tempfile.TemporaryDirectory(prefix='simulation-') as tmp:
        feed = StateFeed(Path(tmp)/'admin.sock')
        server = Server(APP, env=env, options=['--threads', str(threads), '--gpu', '512' if gpu else 'off',
                                               '--inspect-socket', str(Path(tmp)/'admin.sock')])
        try:
            receipt = server.prepared(0, CODE, 'alice-token', proof=PROOF)
            assert receipt['status'] == 'prepared', server.diagnostics()
            native, report = artifact(server, gpu)
            if trace: trace.write_text('')
            expected, results = [state({}), state({})], {}
            for user, depth, steps in [('alice', 0, 0), ('alice', 3, 17), ('bob', 6, 257), ('alice', 10, 1024)]:
                reference = oracle(depth, steps, user)
                response = server.prepared(1, receipt['value'], user+'-token', [depth, steps])
                assert response == dict(status='success', value=reference), (response, server.diagnostics())
                results[user] = reference
                expected.append(state(results))
            if ordinary:
                reference = oracle(2, 3)
                response = server.call(CODE, CONCRETE, 'alice-token', [2, 3])
                assert response == dict(status='success', value=reference), (response, server.diagnostics())
                results['alice'] = reference
                expected.append(state(results))
            for args, message in [(None, 'expected [depth, steps]'), ([-1, 10], 'expected [depth, steps]'),
                                  ([19, 0], 'invalid size'), ([1, 65537], 'invalid size')]:
                assert server.prepared(1, receipt['value'], 'alice-token', args) == dict(status='refusal', value=message)
                expected.append(state(results))
            server.finish()
            feed.finish()
            published = publications(feed)
            assert published == expected, (published, expected)
            return published, report
        finally:
            server.close()
            feed.listener.close()
            feed.thread.join(timeout=5)


class SimulationCpuTests(unittest.TestCase):
    def test_cpu_application_and_complete_state(self):
        exercise(1, ordinary=True)


class SimulationSqlTests(unittest.TestCase):
    def test_recursive_sql_matches_scalar_oracle_and_complete_tables(self):
        from paper.bench.simulation import SCHEMA, sql_state
        query = (ROOT/'paper/bench/simulation-sqlite.sql').read_text()
        with sqlite3.connect(':memory:', isolation_level=None) as conn:
            conn.executescript(SCHEMA)
            for user, values in PARAMETERS.items():
                conn.execute('INSERT INTO scenarios VALUES(?,?,?,?)', (user, *values))
            results = {}
            for user in PARAMETERS:
                for depth, steps in [(0, 0), (3, 17), (6, 257)]:
                    reference = oracle(depth, steps, user)
                    rows = conn.execute(query, dict(who=user, paths=1 << depth, steps=steps)).fetchall()
                    self.assertEqual(rows, [tuple(reference[k] for k in ('sum', 'max', 'above', 'paths'))])
                    results[user] = reference
                    self.assertEqual(sql_state(conn), state(results)['tables'])


class SimulationGpuTests(unittest.TestCase):
    def test_cpu_one_sixteen_and_cuda_identical(self):
        runs = [exercise(1), exercise(16), exercise(1, True)]
        self.assertEqual(runs[0][0], runs[1][0])
        self.assertEqual(runs[0][0], runs[2][0])
        self.assertEqual(len({r[1]['sourceSha256'] for r in runs}), 1)

    def test_real_launches_and_forbidden_write_before_compilation(self):
        with tempfile.TemporaryDirectory(prefix='simulation-driver-') as tmp:
            folder = Path(tmp)
            library, trace = folder/'driver.so', folder/'trace'
            subprocess.run(['gcc', '-shared', '-fPIC', str(ROOT/'tests/service/gpu_faults.c'),
                            '-o', str(library), '-ldl'], check=True)
            env = dict(os.environ, LD_PRELOAD=str(library), JAYDB_TEST_GPU_TRACE=str(trace), JAYDB_BENCH_TIMING='1')
            _, report = exercise(1, True, env, trace)
            events = trace.read_text().splitlines()
            self.assertIn('launch 0', events)
            self.assertIn('sync 0', events)
            print('Simulation forwarding evidence: '+json.dumps(dict(sourceSha256=report['sourceSha256'],
                hasBangs=report['hasBangs'], launches=events.count('launch 0'), synchronizations=events.count('sync 0'))), flush=True)
            feed = StateFeed(folder/'reject.sock')
            server = Server(APP, env=env, options=['--gpu', '512', '--inspect-socket', str(folder/'reject.sock')])
            try:
                self.assertEqual(server.prepared(0, CODE, 'invalid', proof=PROOF)['status'], 'authentication')
                start = len(server.diagnostics())
                trace.write_text('')
                forbidden = CODE.replace('D.Application{"results"}, id, fields(id, stats)',
                                         'D.Application{"results"}, "bob", fields("bob", stats)')
                self.assertNotEqual(CODE, forbidden)
                for prepared in (False, True):
                    response = (server.prepared(0, forbidden, 'alice-token', proof=PROOF) if prepared else
                                server.call(forbidden, CONCRETE, 'alice-token', [2, 8]))
                    self.assertEqual(response, dict(status='certificate', value=None), server.diagnostics())
                errors = server.diagnostics()[start:]
                self.assertIn('PRIMARY_CHECK', errors)
                self.assertNotIn('c_compilation', errors)
                self.assertNotIn('c_emission', errors)
                self.assertEqual(trace.read_text(), '')
                private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
                self.assertFalse(list(private.glob('request-*')))
                server.finish()
                feed.finish()
                self.assertTrue(feed.states)
                self.assertTrue(all(s == state({}) for s in feed.states))
            finally:
                server.close()
                feed.listener.close()
                feed.thread.join(timeout=5)


if __name__ == '__main__':
    unittest.main()
