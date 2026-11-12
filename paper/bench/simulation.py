#!/usr/bin/env python3
"""Certified table-driven random walks versus in-database PostgreSQL/SQLite.
Caller holds the heavy lock and uses fixed-clock.sh. Never extrapolate SQL.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT/'.build/paper-bench/python'))
from paper.bench.run import BUILD, metadata
from paper.bench.workloads import postgres
from tests.service.test_end_to_end import Server
from tests.service.test_gpu import StateFeed
from tests.service.test_simulation import APP, CODE, PROOF, PARAMETERS, artifact, oracle, publications, state

SIZES = [(2, 32), (10, 256), (14, 1024), (16, 16384)]
COLUMNS = ('sum', 'max', 'above', 'paths')
SCHEMA = '''CREATE TABLE scenarios(id text PRIMARY KEY, seed bigint NOT NULL,
  drift bigint NOT NULL, volatility bigint NOT NULL);
CREATE TABLE results(id text PRIMARY KEY, sum bigint NOT NULL, max bigint NOT NULL,
  above bigint NOT NULL, paths bigint NOT NULL);'''


def timed(operation):
    started = time.perf_counter_ns()
    result = operation()
    return result, (time.perf_counter_ns()-started)/1e6


def record(backend, depth, steps, samples, warmup, result, verified=False):
    return dict(backend=backend, depth=depth, paths=1 << depth, steps=steps,
        updates=(1 << depth)*steps, status='measured', samples_ms=samples, warmup_ms=warmup,
        median_ms=statistics.median(samples), range_ms=[min(samples), max(samples)], result=result,
        complete_state_verified=verified)


def sql_state(conn):
    scenarios = [dict(zip(('id', 'seed', 'drift', 'volatility'), row)) for row in
                 conn.execute('SELECT id,seed,drift,volatility FROM scenarios ORDER BY id').fetchall()]
    results = [dict(zip(('id', *COLUMNS), row)) for row in
               conn.execute('SELECT id,sum,max,above,paths FROM results ORDER BY id').fetchall()]
    return [dict(name='results', rows=results), dict(name='scenarios', rows=scenarios)]


def sql_run(engine, conn, output, references, repeats, timeout, save):
    token = '?' if engine == 'sqlite' else '%s'
    if engine == 'postgresql':
        conn.execute(SCHEMA.replace('CREATE TABLE', 'CREATE TEMP TABLE'))
        conn.execute((ROOT/'paper/bench/simulation-postgres.sql').read_text())
        conn.execute(f"SET statement_timeout='{int(timeout*1000)}ms'")
    else:
        conn.executescript(SCHEMA)
    for user, values in PARAMETERS.items():
        conn.execute(f'INSERT INTO scenarios VALUES ({",".join([token]*4)})', (user, *values))
    query = ((ROOT/'paper/bench/simulation-sqlite.sql').read_text() if engine == 'sqlite'
             else 'SELECT * FROM simulate(%s,%s,%s)')
    controls = {}
    for user in PARAMETERS:
        for depth, steps in ((0, 0), (3, 17)):
            params = dict(who=user, paths=1 << depth, steps=steps) if engine == 'sqlite' else (user, depth, steps)
            reference = oracle(depth, steps, user)
            assert conn.execute(query, params).fetchall() == [tuple(reference[k] for k in COLUMNS)]
            controls[user] = reference
            assert sql_state(conn) == state(controls)['tables']
            output.setdefault('sql_controls', []).append(dict(backend=engine, user=user, depth=depth,
                steps=steps, result=reference, complete_tables=sql_state(conn)))
    conn.execute('DELETE FROM results')
    deadline, capped, last, current = 0, False, None, {}
    if engine == 'sqlite':
        conn.set_progress_handler(lambda: int(time.perf_counter() > deadline), 10000)
    for depth, steps in SIZES:
        if capped:
            output['records'].append(dict(backend=engine, depth=depth, steps=steps,
                paths=1 << depth, status='not run', reason=f'not run beyond {last} updates (earlier SQL timeout)', timeout_s=timeout))
            save(); continue
        samples, warmup = [], []
        try:
            for trial in range(repeats+1):
                deadline = time.perf_counter()+timeout
                params = dict(who='alice', paths=1 << depth, steps=steps) if engine == 'sqlite' else ('alice', depth, steps)
                rows, elapsed = timed(lambda: conn.execute(query, params).fetchall())
                assert rows == [tuple(references[f'{depth}:{steps}'][k] for k in COLUMNS)], (engine, rows)
                assert sql_state(conn) == state({'alice': references[f'{depth}:{steps}']})['tables']
                current = {'alice': references[f'{depth}:{steps}']}
                (samples if trial else warmup).append(elapsed)
            last = (1 << depth)*steps
            output['records'].append(record(engine, depth, steps, samples, warmup, references[f'{depth}:{steps}'], verified=True))
        except Exception as error:
            # Only actual engine cancellation is a cap; syntax/data failures abort.
            is_timeout = (isinstance(error, sqlite3.OperationalError) and str(error) == 'interrupted')
            is_timeout |= getattr(error, 'sqlstate', None) == '57014'
            if not is_timeout: raise
            capped = True
            deadline = time.perf_counter()+timeout
            assert sql_state(conn) == state(current)['tables'], 'timeout did not roll back'
            output['records'].append(dict(backend=engine, depth=depth, steps=steps, paths=1 << depth,
                status='timeout', timeout_s=timeout, completed_samples_ms=samples, warmup_ms=warmup,
                last_verified_updates=last, diagnostic=str(error)))
        save()
        print(engine, depth, steps, output['records'][-1].get('median_ms', output['records'][-1]['status']), flush=True)
    if engine == 'sqlite': conn.set_progress_handler(None, 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--sql-timeout', type=float, default=10)
    args = parser.parse_args()
    assert args.repeats >= 3 and args.sql_timeout > 0
    assert 'JAYDB_BENCH_FREQUENCY_ORIGINAL' in os.environ, 'use fixed-clock.sh'
    assert not os.environ.get('LD_PRELOAD'), 'time the unwrapped real CUDA driver'
    BUILD.mkdir(parents=True, exist_ok=True)
    references = {f'{d}:{s}': oracle(d, s, vector=True) for d, s in SIZES}
    for user in PARAMETERS:
        assert oracle(3, 17, user) == oracle(3, 17, user, vector=True)
    run_metadata = metadata(1)
    run_metadata.update(threads=[1, 16], gpu=['off', '512 MiB'])
    output = dict(metadata=run_metadata, sizes=[dict(depth=d, steps=s, paths=1 << d) for d, s in SIZES],
        repeats=args.repeats, warmups=1, gpu_mib=512, parameters=PARAMETERS, oracle=references,
        oracle_method='Independent scalar Python cross-check plus NumPy uint64, explicit U32 masks, every path and step',
        source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in
            [*APP.glob('*.bend'), *Path(__file__).parent.glob('simulation*.sql'), Path(__file__),
             ROOT/'tests/service/test_simulation.py']},
        settings=dict(cuda=dict(corpus_mib=512, host_threads=1, clock_fixed=False,
            device=subprocess.check_output(['nvidia-smi', '--query-gpu=name,driver_version,memory.total', '--format=csv'], text=True)),
            cpu_threads=[1, 16], numpy=__import__('numpy').__version__), preparations=[], records=[], published_states={}, limitations=[
            'JayDB2 RAM state, PostgreSQL temporary tables (no table WAL), SQLite :memory:; no durability comparison.',
            'JayDB2 fresh child per request, fresh authentication, integrity checks and complete publication; proof admission timed separately.',
            'SQL execute/fetch includes parameter reads, simulation, upsert and returning all aggregates; no host-language UDF.',
            'SQL is an arithmetic baseline without equivalent proof admission or authentication/RLS.',
            'PostgreSQL PL/pgSQL is interpreted; SQLite recursive CTE is not designed for heavy numerical compute.',
            'One session, one excluded warmup and at least three samples per measured size; complete state checked outside timing.',
            'CPU clock policy fixed by wrapper; GPU clock unfixed and device drives desktop; no general speedup claim.',
            f'SQL statement timeout {args.sql_timeout}s; later sizes not run after first timeout; no extrapolation.'])
    def save():
        args.output.parent.mkdir(parents=True, exist_ok=True)
        temp = args.output.with_suffix('.tmp')
        temp.write_text(json.dumps(output, indent=2, allow_nan=False)+'\n')
        temp.replace(args.output)
    save()
    hashes = set()
    for name, threads, gpu in [('cpu-1', 1, False), ('cpu-16', 16, False), ('cuda', 1, True)]:
        with tempfile.TemporaryDirectory(prefix='simulation-bench-') as tmp:
            feed = StateFeed(Path(tmp)/'admin.sock')
            server = Server(APP, options=['--threads', str(threads), '--gpu', '512' if gpu else 'off',
                                          '--inspect-socket', str(Path(tmp)/'admin.sock')])
            try:
                assert server.prepared(0, CODE, 'invalid', proof=PROOF)['status'] == 'authentication'
                receipt, elapsed = timed(lambda: server.prepared(0, CODE, 'alice-token', proof=PROOF))
                assert receipt['status'] == 'prepared', server.diagnostics()
                _, report = artifact(server, gpu)
                hashes.add(report['sourceSha256'])
                output['preparations'].append(dict(backend=name, threads=threads, elapsed_ms=elapsed, artifact=report))
                expected = [state({})]*3
                for depth, steps in SIZES:
                    samples, warmup = [], []
                    reference = references[f'{depth}:{steps}']
                    for trial in range(args.repeats+1):
                        response, elapsed = timed(lambda: server.prepared(1, receipt['value'], 'alice-token', [depth, steps]))
                        assert response == dict(status='success', value=reference), (response, server.diagnostics())
                        expected.append(state({'alice': reference}))
                        (samples if trial else warmup).append(elapsed)
                    output['records'].append(record(name, depth, steps, samples, warmup, reference))
                    save()
                    print(name, depth, steps, statistics.median(samples), flush=True)
                server.finish(); feed.finish()
                published = publications(feed)
                assert published == expected, 'complete published states differ'
                output['published_states'][name] = published
                for row in output['records']:
                    if row['backend'] == name: row['complete_state_verified'] = True
            finally:
                server.close()
        assert len(hashes) == 1, 'CPU/CUDA emitted C differs'
        save()
    with postgres() as (_, _, conn, settings):
        output['settings']['postgresql'] = dict(settings, tables='TEMP', admission='none',
            psycopg=__import__('psycopg').__version__)
        sql_run('postgresql', conn, output, references, args.repeats, args.sql_timeout, save)
    with sqlite3.connect(':memory:', isolation_level=None) as conn:
        output['settings']['sqlite'] = dict(version=sqlite3.sqlite_version, storage=':memory:',
            journal_mode=conn.execute('PRAGMA journal_mode').fetchone()[0], implementation='recursive CTE; no Python UDF')
        sql_run('sqlite', conn, output, references, args.repeats, args.sql_timeout, save)
    save()


if __name__ == '__main__':
    main()
